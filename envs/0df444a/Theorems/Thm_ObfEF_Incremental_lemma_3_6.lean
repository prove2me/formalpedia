-- Prove2me | Theorems.Thm_ObfEF_Incremental_lemma_3_6
-- name    : ObfEF.Incremental.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:57:54.04577+00:00
-- url     : https://prove2.me/theorems/25880e34-fc3e-4c78-9ff3-30bd0fc3e0f5
-- title:
--   Lemma 3.6 — a polynomial-time algorithm turns an EF proof of Eqv into a width-three derivation with ≤ c_F(L+il+s) lines of size ≤ c_F
-- statement:
--   There are a constant $c_F$ and a polynomial-time algorithm that, for all circuits $C_0$ and $C_1$ over $B$ with $il\ge1$ inputs, $ol$ outputs and size at most $s$, maps every Extended Frege proof $\pi$ of $\mathrm{Eqv}_{C_0,C_1}$ of size $L$ to a derivation $\theta$ of width three for $C_0$ and $C_1$ (Definition 3.5) with
--   $$|\theta|\le c_F\,(L+il+s)\ \text{lines, each of size at most } c_F.$$
--   The algorithm reads the binary codes of $C_0$, $C_1$ and $\pi$ and writes the code of $\theta$; it is a single machine with a single polynomial time bound, correct on every input with $il\ge1$.
--
--   This is the proof-theoretic half of the rewriting theorem: it localises a short Extended Frege equivalence proof into constant-size inferences that each involve at most three variables after unfolding at most three definitions.
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm (random-access machine with O(log(il+2))-bit words, p. 24) → a function A : List Bool → List Bool with QAlgorithms.Complexity.PolyTimeComputable A (multi-stack Turing machine, polynomial time bound), on the fixed codes Enc.lemma36Input C₀ C₁ π and Enc.list Enc.fml θ; reason: random-access machines with logarithmic words and Turing machines simulate each other with polynomial overhead; the codes are binary and of polynomial length
--   - reading: a canonical topological order of a circuit (Definitions 2.7, 3.3), not further specified → the order of the circuit's vertex numbering, inputs first (Circuit stores its noninput vertices in a topological order); reason: every circuit of Definition 2.1 is represented once a topological order is fixed, and that order is the canonical one
--   - reading: |φ| is the number of symbols of φ → Fml.size counts each occurrence of a variable, of ⊥ and of → once, parentheses not counted; reason: the paper does not say whether parentheses count; counting them changes sizes by at most a factor 3, absorbed by the constants
--   - encoding: the variables x_r, y^b_v of the derivation and the auxiliary variables y_i, z_i of Eqv_{C₀,C₁} → x_r = var r, y^b_j = var (il + 2j + b); the auxiliary variables of Eqv are var (il + Nat.pair k (2·idx(v) + b)); reason: a fixed injective naming; renaming variables preserves EF proofs and sizes
--   - reading: 'its first lines are the definitions of the variables of the noninput vertices of C₀ and C₁' → the first |C₀| + |C₁| lines are a permutation of these definitions; reason: the paper fixes no order among the definitions
--   - encoding: every EF proof of size L, circuits of size at most s → every π with IsEFProof π (Eqv C₀ C₁), L = proofSize π, for every s ≥ |C₀|, |C₁|; reason: same quantification
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 49, Lemma 3.6

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula
import Definitions.Def_ObfEF_Incremental_ExtendedFrege
import Definitions.Def_ObfEF_Incremental_Eqv
import Definitions.Def_ObfEF_Incremental_Derivation
import Definitions.Def_ObfEF_Incremental_Encoding

namespace ObfEF.Incremental

/-- Lemma 3.6 (Derivations of Width Three). There are a constant `c_F` and a polynomial-time
algorithm `A` that, for all circuits `C₀, C₁` over `B` with `il ≥ 1` inputs, `ol` outputs and size
at most `s`, maps (the code of `C₀`, `C₁` and) every EF proof `π` of `Eqv_{C₀,C₁}` of size `L` to
(the code of) a derivation of width three for `C₀` and `C₁` with at most `c_F(L + il + s)` lines,
each of size at most `c_F`. -/
theorem lemma_3_6 :
    ∃ (cF : ℕ) (A : List Bool → List Bool), QAlgorithms.Complexity.PolyTimeComputable A ∧
      ∀ (il ol s : ℕ) (C₀ C₁ : Circuit (Fin il) ol), 1 ≤ il → C₀.size ≤ s → C₁.size ≤ s →
        ∀ π : List Fml, IsEFProof π (Eqv C₀ C₁) →
          ∃ θ : List Fml, A (Enc.lemma36Input C₀ C₁ π) = Enc.list Enc.fml θ ∧
            IsDerivationW3 C₀ C₁ θ ∧ θ.length ≤ cF * (proofSize π + il + s) ∧
            ∀ φ ∈ θ, φ.size ≤ cF := by sorry

end ObfEF.Incremental
