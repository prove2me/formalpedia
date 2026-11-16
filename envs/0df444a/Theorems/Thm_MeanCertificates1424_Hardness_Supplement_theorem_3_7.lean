-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_3_7
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:58:03.597235+00:00
-- url     : https://prove2.me/theorems/3c30eb1d-6518-4f2c-b59f-a5bae46ddf8b
-- title:
--   Theorem 3.7 — hardness of hidden depth and of the recovery radius, with Corollary 3.9 (no EPTAS/FPTAS)
-- statement:
--   Let $\Psi_G(M)=\max_{|S|\le M}\sum_{v\in S}d_G(v,V\setminus S)$ for $0\le M<n$.
--
--   1. Deciding whether $\Psi_G(M)\ge t$ for a given integer $t$ is in NP on connected graphs; it is NP-complete, and W[1]-hard parameterized by $M$, even for even $M$ on connected split graphs of diameter two.
--   2. Consequently, computing the uniform minimax radius $R^*_\emptyset(G,b,1,0)$ (no audits, $L=1$, $\epsilon=0$) is NP-hard and W[1]-hard in $b$ on connected split graphs of diameter two, even when $2b<n$; any fixed bound $b\le\rho n$ with rational $\rho\in(0,1)$ may be imposed.
--   3. (Corollary 3.9.) Unless FPT $=$ W[1], neither the upper endpoint on the instances of Theorem 3.5 nor the recovery radius on the instances of item 2 admits a relative-error approximation scheme with running time $f(1/\xi)\,n^{O(1)}$. A fully polynomial scheme for either would imply P $=$ NP.
--
--   Item 3 is the efficient-approximation-scheme clause of the introductory Theorem 1.3. The theorem locates the hardness of worst-case recovery in the combinatorial depth $\Psi_G$.
--
--   **Formalization Note** "Computing $R^*$" is expressed by its decision version $R^*\ge\theta$ for rational $\theta$. Schemes are required on every instance of the class, with relative error $|a-v|\le\xi v$ for every rational $\xi>0$.
--
--   Differences from the source:
--   - encoding: W[1]-hard → fpt many-one reducible from p-Clique with the new parameter bounded by a computable function of k; reason: standard W[1]-completeness of p-Clique; the brief prescribes this equivalence
--   - reading: Upper-Mean is hard on a restricted class → every NP language (resp. p-Clique) reduces to the restricted language by a reduction whose outputs always lie in the class; reason: hardness of a problem restricted to a class means reductions into that class
--   - reading: computing R*_∅(G,b,1,0) is NP-hard and W[1]-hard → deciding R*_∅(G,b,1,0) ≥ θ for rational θ is NP-hard and W[1]-hard on the class; reason: hardness of the decision version is what makes computing hard
--   - encoding: whether Ψ_G(M) is at least a given integer → threshold t a natural number; reason: Ψ_G(M) ≥ 0, so negative thresholds are trivial yes-instances
--   - encoding: Unless FPT = W[1] → the scheme implies that p-Clique is fixed-parameter tractable; reason: standard equivalence FPT = W[1] iff p-Clique ∈ FPT
--   - reading: running time f(1/ξ) n^{O(1)} → time f(⌈1/ξ⌉)·(input length + 1)^c with f computable and c fixed; reason: binary input overhead included, as prescribed by the brief
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.7 and Corollary 3.9, printed p.10 (PDF p.12); EPTAS clause of Theorem 1.3, printed p.2 (PDF p.4)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 3.7, printed p.10 / PDF p.12, with Corollary 3.9 (printed p.10, PDF p.12; the
EPTAS clause of introductory Theorem 1.3, printed p.2 / PDF p.4).
1. Deciding `Ψ_G(M) ≥ t` (`0 ≤ M < n`, integer `t`) is in NP on connected graphs, and is
   NP-complete and W[1]-hard in `M` even for even `M` on connected split graphs of diameter two.
2. Deciding `R*_∅(G, b, 1, 0) ≥ θ` is NP-hard and W[1]-hard in `b` on connected split graphs of
   diameter two with `2b < n`, also with `b ≤ ρ n` for every fixed rational `ρ ∈ (0,1)`.
3. Unless FPT = W[1], neither the upper endpoint on the instances of Theorem 3.5 nor the radius
   on the instances of item 2 admits an EPTAS; an FPTAS for either would imply P = NP. -/
theorem theorem_3_7 :
    (InNP (DepthLang @ConnGraph) ∧ InNP (DepthLang @EvenSplitDiamTwo) ∧
      NPHardOn (DepthLang @EvenSplitDiamTwo) (DepthOut @EvenSplitDiamTwo) ∧
      W1HardOn (DepthLang @EvenSplitDiamTwo) depthParam (DepthOut @EvenSplitDiamTwo)) ∧
    (NPHardOn (RadLang 1) (RadOut 1) ∧ W1HardOn (RadLang 1) radParam (RadOut 1)) ∧
    (∀ ρ : ℚ, 0 < ρ → ρ < 1 →
      NPHardOn (RadLang ρ) (RadOut ρ) ∧ W1HardOn (RadLang ρ) radParam (RadOut ρ)) ∧
    (EPTAS (ZeroSplit 1) encInstance (fun I => (Hardness.upper I).toReal) → FPTeqW1) ∧
    (EPTAS (fun R : RadInst => RadClass 1 R.G R.b) (fun R => encGraph R.G ++ encNat R.b)
      (fun R => (minimaxRadius R.G R.b 1 0 ∅ (uniformW R.n)).toReal) → FPTeqW1) ∧
    (FPTAS (ZeroSplit 1) encInstance (fun I => (Hardness.upper I).toReal) → PeqNP) ∧
    (FPTAS (fun R : RadInst => RadClass 1 R.G R.b) (fun R => encGraph R.G ++ encNat R.b)
      (fun R => (minimaxRadius R.G R.b 1 0 ∅ (uniformW R.n)).toReal) → PeqNP) := by sorry

end MeanCertificates1424.Hardness.Supplement
