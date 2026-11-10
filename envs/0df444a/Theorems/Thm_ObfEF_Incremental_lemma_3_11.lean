-- Prove2me | Theorems.Thm_ObfEF_Incremental_lemma_3_11
-- name    : ObfEF.Incremental.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:58:21.832376+00:00
-- url     : https://prove2.me/theorems/2f4e0787-9afb-45a6-aaf0-94fa9a76f858
-- title:
--   Lemma 3.11 (= Theorem 1.2) — incremental changes with three-wire supports between the paddings of EF-equivalent circuits
-- statement:
--   Let the block length $c_x\ge1$ of the padding be chosen as on p. 52: every formula over $\{\to,\bot\}$ of size at most $c_F$ is computed by the last instruction of a straight-line program of $c_x$ instructions $0,1,\neg a,a\wedge b,a\vee b$, for the line-size constant $c_F$. There is a constant $c_0$ such that for all $il,ol,s,L\ge1$, all circuits $C_0$ and $C_1$ over $B=\{\mathrm{AND},\mathrm{OR},\mathrm{NOT}\}$ with $il$ inputs, $ol$ outputs and size at most $s$ such that $\mathrm{Eqv}_{C_0,C_1}$ has an Extended Frege proof of size at most $L$, and every power of two $K\ge c_0(L+il+s)$, there are configurations
--   $$\mathrm{Pad}(C_0)=D_0,\ D_1,\ \dots,\ D_N=\mathrm{Pad}(C_1)\quad\text{of the topology } U_{il,ol,s,K},\qquad N\le c_0K^2,$$
--   such that for every $t\in[N]$ some incremental change $(S,R,\Gamma)$ from $D_{t-1}$ to $D_t$ (Definition 3.1) satisfies
--   $$|S|\le c_0K,\qquad |R|\le3,\qquad |\Gamma_o|,|\Gamma'_o|\le c_0\ \text{ for every output wire } o \text{ of a gate of } S.$$
--   In Lean: there is $c_F$ such that for every $c_x\ge1$ that is a block length for $c_F$ there is $c_0$ with the property above.
--
--   This is the paper's unconditional rewriting theorem (Theorem 1.2): a short Extended Frege proof that two circuits are equivalent converts into a polynomial-length sequence of local changes between their paddings, each controlled by at most three wire values. In the paper it is what lets a gate-by-gate security proof of obfuscation move from $\mathrm{Pad}(C_0)$ to $\mathrm{Pad}(C_1)$ with hybrids that recover only three wire values at a time.
--
--   Differences from the source:
--   - reading: a constant c_x chosen so that every formula over → and ⊥ of size at most c_F is computed by the last instruction of a straight-line program of c_x instructions (p. 52), fixed before Lemma 3.11 → ∃ c_F, ∀ c_x ≥ 1, SLPBound c_F c_x → ∃ c₀, …; reason: the paper fixes c_x only through this property relative to its c_F; the Lean form holds for every admissible choice and implies the form ∃ c_x ≥ 1 ∃ c₀ (a block length exists for every c_F, e.g. c_x = 2c_F + 1)
--   - reading: circuits D_t 'with the topology U_{il,ol,s,K}' → configurations D_t : CName → Bool of U_{il,ol,s,K}, with circuit labels il ol M (D t) over the wiring UPad; reason: the paper identifies a configuration with its circuit (Definition 3.3); arbitrary relabellings of U's graph would be a weaker reading
--   - reading: a canonical topological order of a circuit (Definitions 2.7, 3.3), not further specified → the order of the circuit's vertex numbering, inputs first (Circuit stores its noninput vertices in a topological order); reason: every circuit of Definition 2.1 is represented once a topological order is fixed, and that order is the canonical one
--   - reading: |φ| is the number of symbols of φ → Fml.size counts each occurrence of a variable, of ⊥ and of → once, parentheses not counted; reason: the paper does not say whether parentheses count; counting them changes sizes by at most a factor 3, absorbed by the constants
--   - encoding: real constants c₀ → c₀ : ℕ; reason: a real constant can be rounded up
--   - encoding: 1-based cells, inputs and outputs → 0-based cells in the layout of Pad (cellA … cellF), inputs Fin il, outputs Fin ol; reason: Lean convention; same topology and configurations
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 55, Lemma 3.11 (informal Theorem 1.2, pp. 7-8; c_x: p. 52)

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula
import Definitions.Def_ObfEF_Incremental_ExtendedFrege
import Definitions.Def_ObfEF_Incremental_Eqv
import Definitions.Def_ObfEF_Incremental_GateList
import Definitions.Def_ObfEF_Incremental_IncrementalChange
import Definitions.Def_ObfEF_Incremental_Cells
import Definitions.Def_ObfEF_Incremental_Padding

namespace ObfEF.Incremental

/-- Lemma 3.11 (Incremental Changes Between Paddings; formal Theorem 1.2). The block length `c_x`
of the padding is any constant with the straight-line-program property of p. 52 for the line-size
constant `c_F`. There is a constant `c₀` such that for all `il, ol, s, L ≥ 1`, all circuits `C₀`,
`C₁` over `B` with `il` inputs, `ol` outputs and size at most `s` such that `Eqv_{C₀,C₁}` has an EF
proof of size at most `L`, and every power of two `K ≥ c₀(L + il + s)`, there are configurations
`Pad(C₀) = D₀, D₁, …, D_N = Pad(C₁)` of `U_{il,ol,s,K}` with `N ≤ c₀K²` such that for every
`t ∈ [N]` some incremental change from `D_{t-1}` to `D_t` has a subcircuit of at most `c₀K` gates,
a support of size at most 3, and circuits of size at most `c₀`. -/
theorem lemma_3_11 :
    ∃ cF : ℕ, ∀ cx : ℕ, 1 ≤ cx → SLPBound cF cx →
    ∃ c₀ : ℕ, ∀ (il ol s L : ℕ), 1 ≤ il → 1 ≤ ol → 1 ≤ s → 1 ≤ L →
      ∀ (C₀ C₁ : Circuit (Fin il) ol), C₀.size ≤ s → C₁.size ≤ s →
      (∃ π : List Fml, IsEFProof π (Eqv C₀ C₁) ∧ proofSize π ≤ L) →
      ∀ K : ℕ, (∃ m : ℕ, K = 2 ^ m) → c₀ * (L + il + s) ≤ K →
      ∃ N : ℕ, N ≤ c₀ * K ^ 2 ∧ ∃ D : Fin (N + 1) → Config,
        D 0 = PadC cx il ol s K C₀ ∧ D (Fin.last N) = PadC cx il ol s K C₁ ∧
        ∀ t : Fin N,
          ∃ ch : IncrementalChange (UPad cx il ol s K)
              (labels il ol (Pad.M cx ol s K) (D t.castSucc))
              (labels il ol (Pad.M cx ol s K) (D t.succ)),
            ch.S.card ≤ c₀ * K ∧ ch.R.card ≤ 3 ∧
            ∀ j ∈ ch.S, (ch.Γ j).size ≤ c₀ ∧ (ch.Γ' j).size ≤ c₀ := by sorry

end ObfEF.Incremental
