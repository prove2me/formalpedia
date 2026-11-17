-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_A_3
-- name    : MantriCVQ.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:10:24.053878+00:00
-- url     : https://prove2.me/theorems/17f7edb3-e505-4ba0-ac2f-c1d16b6be6a1
-- title:
--   Theorem A.3 — bounded-error evaluation with noisy code tables: error $1/10$ with $C_\eta^j$ queries; $\delta$-close clean oracle and $\zeta$-error decoder
-- statement:
--   Fix a code family of Definition 3.1 and a noise rate $0\le\eta<1/4$.
--
--   1. There are a constant $C_\eta$ and a uniform quantum algorithm that, on every tree of height $j$ that is valid with noise rate $\eta$, computes the value of the tree with error at most $1/10$, with at most $C_\eta^{\,j}$ leaf queries and in time $C_\eta^{\,j}\,\mathrm{poly}(n,j)$.
--   2. For every fixed $\delta>0$ and $0<\zeta<1$, a unitary $G$ within $\delta$ of the clean oracle $E$ for the values of such trees, in the sense
--   $$\|(G-E)\Pi_0\|\le\delta$$
--   of Claim A.2, and a decoder of their secrets with error at most $\zeta$, have resource bounds of the same form, with constants depending on $\eta$, $\delta$ and $\zeta$.
--
--   Here $\Pi_0$ projects onto the states whose address register holds a valid address (the address of a node of height $j$ whose subtree is valid with noise rate $\eta$) and whose work registers are zero. The algorithm, the unitary and the decoder are the building blocks of the noisy-table algorithm and honest prover of Theorem 7.4.
--
--   **Formalization Note** The registers are those of the base Theorem 5.1: address of a node of height $j$ in an instance of size $n$ and height $h$, then the output qubit (or $m_{j-1}$ output wires for the decoder, $j\ge1$), then work wires, all generated from $(1^n,1^h,1^j)$. The closeness bound is $\|G\psi-E\psi\|\le\delta\|\psi\|$ in the Euclidean norm for every $\psi$ in the range of $\Pi_0$. The decoder's output is the secret, the string whose codeword is within relative distance $\eta$ of the code table.
--
--   Differences from the source:
--   - encoding: a uniform quantum algorithm on every tree of height j valid with noise rate η, error at most 1/10 → circuits A(n, h, j) on address + output + work wires, generated from (1^n, 1^h, 1^j); from |w₀⟩|0⟩|0…0⟩ with the subtree at w₀ valid with noise rate η, the output wire reads the node's value with probability ≥ 9/10; reason: the register convention of the base Theorem 5.1; the instance of height h ≤ h_max(n) fixes the address length
--   - encoding: at most C^j leaf queries and time C^j poly(n, j); constants depending on η, δ, ζ → oracle gates ≤ C^j, circuit size and ancillas ≤ C^j p(n + j), with C a natural number chosen after the code family and η (after δ and ζ in part 2); reason: the base mission's convention for time; a real constant can be rounded up
--   - encoding: a unitary within δ of the clean oracle in the sense of Claim A.2 (operator norm of (G − E)Π₀; also with any reference system) → vecNorm(Gψ − Eψ) ≤ δ·vecNorm(ψ) (Euclidean norm, published KTUnitary.Synth.vecNorm) for every ψ supported on valid addresses with zero work wires and arbitrary output qubit; reason: the operator-norm bound on the range of Π₀ is this inequality; tensoring with the identity on a reference system preserves the operator norm
--   - encoding: a decoder of their secrets with error at most ζ → for j ≥ 1, circuits Dec(n, h, j) from |w₀⟩|0^{m_{j−1}}⟩|0…0⟩ whose measured output wires equal, with probability ≥ 1 − ζ, every s whose codeword is within relative distance η of the code table at w₀; reason: the true secret is the unique such s (distinct codewords have distance 1/2 > 2η)
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem A.3, p. 44 (PDF p. 46); Claim A.2, p. 43 (PDF p. 45)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_nodeValNoisy
import Definitions.Def_AvoidPlast_relDist
import Definitions.Def_KTUnitary_Synth_vecNorm
import Definitions.Def_MantriCVQ_Supplement_cleanOracle
import Definitions.Def_MantriCVQ_Supplement_InRangePi0
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_leafTable
import Definitions.Def_MantriCVQ_QProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem A.3** (Bounded-error evaluation with noisy code tables; Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), Theorem A.3, p. 44 (PDF p. 46); Claim A.2, p. 43 (PDF p. 45)): fix a code
family of Definition 3.1 and `0 ≤ η < 1/4`. There is a uniform quantum algorithm that, on every tree
of height `j` that is valid with noise rate `η`, computes the value of the tree with error at most
`1/10`, with at most `C_η^j` leaf queries and in time `C_η^j poly(n, j)`, for a constant `C_η`. For
every fixed `δ > 0` and `0 < ζ < 1`, a unitary within `δ` of the clean oracle for the values of such
trees in the sense of Claim A.2, and a decoder of their secrets with error at most `ζ`, have resource
bounds of the same form, with constants depending on `η`, `δ` and `ζ`.

**Formalization Note** The registers are those of `MantriCVQ.theorem_5_1`: the address register holds
the address `w₀` of a node of height `j` in an instance of size `n` and height `h`, followed by the
output qubit (or, for the decoder, `m_{j−1}` output wires) and the work wires; the generator reads
`(1^n, 1^h, 1^j)`. Error at most `1/10`: started on `|w₀⟩|0⟩|0…0⟩` with the subtree at `w₀` valid with
noise rate `η`, measuring the output qubit gives the node's value with probability at least `9/10`.
"Within `δ` in the sense of Claim A.2" is `‖(G − E)ψ‖ ≤ δ‖ψ‖` (Euclidean norm) for every `ψ` in the
range of `Π₀`: basis states with a valid address (the subtree at the address is valid with noise rate
`η`), all work wires `0`, and an arbitrary output qubit; `E` is the clean oracle of the noisy values.
A bound of this operator form on the system alone gives the same bound with any reference system,
since it tensorizes. The Euclidean norm is the published `KTUnitary.Synth.vecNorm` and the relative
distance the published `AvoidPlast.relDist`. The decoder, for `j ≥ 1`, started on `|w₀⟩|0^{m_{j−1}}⟩|0…0⟩`, outputs on its
`m_{j−1}` output wires, with probability at least `1 − ζ`, the node's secret: the string `s` whose
codeword is within relative distance `η` of the code table (it is unique). "Queries" are oracle gates,
"time" is circuit size and ancilla count, and `poly(n, j)` is a polynomial in `n + j`; the constants
are natural numbers. -/
theorem theorem_A_3 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d)
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 4) :
    (∃ (Cη : ℕ) (anc : ℕ → ℕ → ℕ → ℕ)
      (A : (n h j : ℕ) → Circ G (addrLen (dimsRange n j (h - j)) + (1 + anc n h j)))
      (p : Polynomial ℕ),
      (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
        f (tup [unary n, unary h, unary j]) = encNat (anc n h j) ++ (A n h j).enc) ∧
      ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
        (A n h j).size ≤ Cη ^ j * p.eval (n + j) ∧ anc n h j ≤ Cη ^ j * p.eval (n + j) ∧
        (A n h j).queries ≤ Cη ^ j ∧
        ∀ (O : Oracle) (w₀ : Addr (dimsRange n j (h - j))),
          ValidNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀) →
          (nodeValNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀) = true →
            (9 : ℝ) / 10 ≤ probOne ((A n h j).run O
              (ket _ (Addr.toStr _ w₀ ++ false :: List.replicate (anc n h j) false)))
              (Fin.natAdd _ ⟨0, by omega⟩)) ∧
          (nodeValNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀) = false →
            probOne ((A n h j).run O
              (ket _ (Addr.toStr _ w₀ ++ false :: List.replicate (anc n h j) false)))
              (Fin.natAdd _ ⟨0, by omega⟩) ≤ 1 / 10)) ∧
    ∀ δ : ℝ, 0 < δ → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ (K : ℕ) (p : Polynomial ℕ) (ancU : ℕ → ℕ → ℕ → ℕ)
        (U : (n h j : ℕ) → Circ G (addrLen (dimsRange n j (h - j)) + (1 + ancU n h j)))
        (ancD : ℕ → ℕ → ℕ → ℕ)
        (Dec : (n h j : ℕ) → Circ G (addrLen (dimsRange n j (h - j)) + (dim n (j - 1) + ancD n h j))),
        (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
          f (tup [unary n, unary h, unary j]) = encNat (ancU n h j) ++ (U n h j).enc) ∧
        (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
          f (tup [unary n, unary h, unary j]) = encNat (ancD n h j) ++ (Dec n h j).enc) ∧
        ∀ n h j : ℕ, 1 ≤ n → j ≤ h → h ≤ hmax n →
          (U n h j).size ≤ K ^ j * p.eval (n + j) ∧ ancU n h j ≤ K ^ j * p.eval (n + j) ∧
          (U n h j).queries ≤ K ^ j ∧
          (Dec n h j).size ≤ K ^ j * p.eval (n + j) ∧ ancD n h j ≤ K ^ j * p.eval (n + j) ∧
          (Dec n h j).queries ≤ K ^ j ∧
          (∀ (O : Oracle) (ψ : QState (addrLen (dimsRange n j (h - j)) + (1 + ancU n h j))),
            InRangePi0 (ValidNoisy C.code η (dimsRange n 0 j) (leafTable O n)) ψ →
            KTUnitary.Synth.vecNorm ((U n h j).run O ψ -
                cleanOracle (nodeValNoisy C.code η (dimsRange n 0 j) (leafTable O n)) ψ) ≤
              δ * KTUnitary.Synth.vecNorm ψ) ∧
          (1 ≤ j → ∀ (O : Oracle) (w₀ : Addr (dimsRange n j (h - j))),
            ValidNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w₀) →
            ∀ s : Bits (dim n (j - 1)),
              AvoidPlast.relDist (fun x : Bits (dim n (j - 1)) =>
                  nodeValNoisy C.code η (dimsRange n 0 (j - 1)) (leafTable O n)
                    (Addr.toStr _ w₀ ++ false :: List.ofFn x)) (C.code (dim n (j - 1)) s) ≤ η →
              1 - ζ ≤ (bornPMF ((Dec n h j).run O
                  (ket _ (Addr.toStr _ w₀ ++ List.replicate (dim n (j - 1) + ancD n h j) false)))
                ((List.finRange (dim n (j - 1))).map fun i =>
                  Fin.natAdd (addrLen (dimsRange n j (h - j))) (Fin.castAdd (ancD n h j) i))
                (dim n (j - 1)) s).toReal) := by sorry

end MantriCVQ.Supplement
