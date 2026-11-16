-- Prove2me | Theorems.Thm_LIPAlgorithm_Supplement_theorem_8_15
-- name    : LIPAlgorithm.Supplement.theorem_8_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:56:07.762199+00:00
-- url     : https://prove2.me/theorems/d9da78ac-50f6-40f0-adbc-3dfe3f97f2a3
-- title:
--   Theorem 8.15 — quantum LIP: an isomorphism and generators of $\mathrm{Aut}(L_1)$, or $\emptyset$, in time $O(n^2\log n)^{n/3}$ with QRAM of size $O(n^2\log n)^{n/3}$
-- statement:
--   Let $n\ge1$ and let $G_1,G_2\in\mathbb Z^{n\times n}$ be integral positive definite Gram matrices (rank-$n$ integral lattices) of encoding length $\ell$. In the QRAM model there are one hybrid quantum–classical machine $M$ and constants $C,K\in\mathbb N$, $c>0$, all fixed before the input, such that the run of $M$ on input $G_1,G_2$ satisfies the following.
--
--   1. Every branch of positive probability halts with cost at most
--   $$\Big\lceil \big(C n^2\log(n+2)\big)^{n/3}\,(\ell+1)^K\Big\rceil$$
--   and QRAM size at most $\lceil (C n^2\log(n+2))^{n/3}\rceil$ cells.
--   2. With probability at least
--   $$1-2^{-c\,n\log n}$$
--   the output is either an isomorphism $O_0\in\mathrm{Iso}(G_1,G_2)$ together with a list of generators of $\mathrm{Aut}(G_1)$ (a list whose generated subgroup of $GL_n(\mathbb Z)$ is exactly $\mathrm{Aut}(G_1)$), or $\emptyset$ when $G_1$ and $G_2$ are not isomorphic.
--
--   Since $\mathrm{Iso}(G_1,G_2)=O_0\,\mathrm{Aut}(G_1)$, the output describes the whole isomorphism coset. This is the paper's quantum main result (Theorem 1.2): the general lattice isomorphism problem in time $O(n^2\log n)^{n/3}$, against $O(n\sqrt{\log n})^n$ classically (Theorem 1.1).
--
--   **Formalization Note** The QRAM model is the definition `qProb` of this mission; the bounds are worst case over all measurement outcomes. $\mathrm{Aut}(G_1)$ is the subgroup `autGroup` of the unit group of integer matrices. The output is the list $O_0, g_1, \dots, g_k$ in the published encoding `encMatList`, or the empty list for $\emptyset$; it is nonempty exactly in the isomorphic case.
--
--   Differences from the source:
--   - reading: In the QRAM model, there is a quantum algorithm → one hybrid machine M of qProb (a TM2 controller fixed before the input, quantum calls over {H, T, CNOT} and unit-cost QRAM gates), with C, K, c chosen before the instance; reason: §8.1 fixes the standard circuit model with cost = gates + oracle calls + QRAM calls; the classical control is the base mission's TM2
--   - encoding: runs in time O(n² log n)^{n/3}, up to polynomial factors in the input encoding length → cost at most budgetQ C K n ℓ = ⌈(C·n²·log(n+2))^{n/3}·(ℓ+1)^K⌉; reason: footnote 2, Remark 2.2; log(n+2) replaces log n, which is 0 at n = 1
--   - reading: with QRAM of size O(n² log n)^{n/3}, up to polynomial factors in the input encoding length → at most qramBound C n = ⌈(C·n²·log(n+2))^{n/3}⌉ cells, no polynomial factor; reason: the sentence is ambiguous about whether the polynomial factor also qualifies the QRAM size; the stronger reading is taken, matching Theorem 8.7 and Remark 2.2 (which concerns running times)
--   - reading: running time of a quantum algorithm → worst case: qProb … (fun _ => True) = 1, i.e. every branch of positive probability halts within the cost and QRAM bounds; reason: the recursion runs capped subroutines (Theorem 8.7, Lemma 8.4(ii)); this is the stronger reading
--   - encoding: rank-n integral lattices L1, L2 → n ≥ 1 and integral positive definite Gram matrices G₁, G₂ (published IsGram); reason: §2.2, pp.10–11; rank 0 is the degenerate empty case
--   - encoding: probability at least 1 − 2^{−Ω(n log n)} → probability at least 1 − 2^{−c·n·log n} with c > 0 chosen before the instance and log natural; reason: as in the published goal theorem_1_1; a change of log base rescales c
--   - reading: generators of Aut(L1) → a list gens of units of the integer matrix ring with Subgroup.closure gens = autGroup G₁ (equality); reason: a generating set of a group generates exactly that group; no bound on the length of the list is stated
--   - encoding: it outputs an isomorphism O0 ∈ Iso(L1, L2) together with generators of Aut(L1), or outputs ∅ if the lattices are not isomorphic → output encMatList (O₀ :: gens) with O₀ ∈ isoSet G₁ G₂, or encMatList [] when isoSet G₁ G₂ = ∅; reason: the published output encoding; the output is nonempty exactly in the isomorphic case
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 8.15, p.49 (PDF p.52); Theorem 1.2, p.2 (PDF p.5)

import Mathlib
import Definitions.Def_LIPAlgorithm_Gram
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_Supplement_qProb
import Definitions.Def_LIPAlgorithm_Supplement_budgetQ
import Definitions.Def_LIPAlgorithm_Supplement_autGroup

namespace LIPAlgorithm

namespace Supplement

/-- **Theorem 8.15 (= Theorem 1.2), quantum LIP with automorphism generators.** Aggarwal, Jiang, Li, Liu,
*An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027 submission (manuscript
sha256 61ee52aa…), Theorem 8.15, p.49 (PDF p.52); informally Theorem 1.2, p.2 (PDF p.5).

One hybrid QRAM machine and constants `C`, `K`, `c > 0`, before the instance: for every `n ≥ 1` and all
integral positive definite `G₁`, `G₂` of encoding length `ℓ`, every branch of positive probability halts
within cost `⌈(C·n²·log(n+2))^{n/3}·(ℓ+1)^K⌉` and QRAM size `⌈(C·n²·log(n+2))^{n/3}⌉` cells, and with
probability at least `1 − 2^{−c·n·log n}` the output is the list `O₀ :: gens` with `O₀ ∈ Iso(G₁, G₂)`
and `gens` generating `Aut(G₁)`, or the empty list ("∅") when `G₁`, `G₂` are not isomorphic.

**Formalization Note.** The model is `qProb`, as in `theorem_8_7`. "Generators of Aut(L1)" is a list
of units whose generated subgroup *equals* `autGroup G₁`; no bound on its length is claimed. The
output is nonempty exactly in the isomorphic case, so the encoding is unambiguous. "Up to polynomial
factors in the input encoding length" is applied to the running time (Remark 2.2), not to the QRAM
size. `log(n+2)` replaces `log n` in the budgets; the logarithm in `2^{−c·n·log n}` is natural. -/
theorem theorem_8_15 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ) (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G₁ G₂ : Gram n), 1 ≤ n → IsGram G₁ → IsGram G₂ →
        let inp := encInst G₁ G₂
        let B := budgetQ C K n (encInst G₁ G₂).length
        let S := qramBound C n
        qProb M inp B S (fun _ => True) = 1 ∧
        1 - (2 : ℝ) ^ (-(c * n * Real.log n)) ≤
          qProb M inp B S fun out =>
            (isoSet G₁ G₂ = ∅ ∧ out = encMatList ([] : List (Gram n))) ∨
              ∃ (O₀ : Gram n) (gens : List (Matrix (Fin n) (Fin n) ℤ)ˣ),
                O₀ ∈ isoSet G₁ G₂ ∧
                Subgroup.closure {u | u ∈ gens} = autGroup G₁ ∧
                out = encMatList (O₀ :: gens.map fun u => (u : Matrix (Fin n) (Fin n) ℤ)) := by sorry

end Supplement

end LIPAlgorithm
