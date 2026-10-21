-- Prove2me | Theorems.Thm_JointMixND_QuadOT_proof_theorem_4_symmetrize
-- name    : JointMixND.QuadOT.proof_theorem_4_symmetrize
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:49.404002+00:00
-- url     : https://prove2.me/theorems/923bc1e5-0c97-4cd5-a76c-23ddf1356e08
-- title:
--   Proof of Theorem 4, p. 27 — symmetrizing by a uniform random permutation does not increase sup_μ C²_μ
-- statement:
--   Let $F$ be a distribution on $\mathbb R$ with finite variance, let $\mathcal M$ be a symmetric set of probabilities on $2^{[n]}$, and let $\mathbf X$ be any random vector with identical marginals $F$. Let $\Pi$ be uniformly distributed on the permutation group $\mathfrak S_n$ and independent of $\mathbf X$, and put $\mathbf X^\Pi=(X_{\Pi(1)},\dots,X_{\Pi(n)})$. Then
--   $$\sup_{\mu\in\mathcal M}C^2_\mu(\mathbf X^\Pi)\le\sup_{\mu\in\mathcal M}C^2_\mu(\mathbf X).$$
--
--   This is the first step of the proof of Theorem 4: it reduces the search for a minimizer of (11) to exchangeable vectors. No joint-mix assumption is made on $\mathbf X$.
--
--   **Formalization Note** The law of $\mathbf X^\Pi$ is `symmetrize P` $=\frac1{n!}\sum_{\pi}\operatorname{law}(\mathbf X_\pi)$ for $\mathbf X\sim P$. Finite variance of $F$ (§4's standing assumption) makes all quadratic costs finite real numbers.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 27, Proof of Theorem 4 (first claim)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Problems

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 4, p. 27, first claim. For a symmetric uncertainty set `𝓜` and any random
vector `X` with identical marginals `F` of finite variance, the symmetrized vector `X^Π`
(`Π` uniform on the permutations, independent of `X`; its law is `symmetrize P`) has worst-case
quadratic cost at most that of `X`. -/
theorem proof_theorem_4_symmetrize {n : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF2 : MemLp id 2 F)
    (M : Set (Finset (Fin n) → ℝ)) (hM : M ⊆ ProbOnSubsets n) (hsymm : IsSymmetric M)
    (P : Measure (Fin n → ℝ)) (hP : IsCoupling F P) :
    worstCost (fun t => t ^ 2) M (symmetrize P) ≤ worstCost (fun t => t ^ 2) M P := by sorry

end JointMixND.QuadOT
