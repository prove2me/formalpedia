-- Prove2me | Theorems.Thm_GaussPolyReg_Approx_theorem_3_5
-- name    : GaussPolyReg.Approx.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:42:57.28246+00:00
-- url     : https://prove2.me/theorems/fe84dc40-0b4b-443b-a45f-b2a4ebf90249
-- title:
--   Theorem 3.5 — ultrapower regularity and countable joint convergence
-- statement:
--   Choose an orthonormal basis $[e_{n,i}]$ of each positive-grade primitive space, with arbitrary index set $I$. For every $d\in\mathbb N$,
--
--   $$\{[\psi_\alpha(e_n)]:\operatorname{gr}(\alpha)=d\}\text{ is an orthonormal basis of }\mathcal H_d.$$
--
--   For any countable family $[p_{n,k}]\in\mathcal H_{d_k}$, let $c_{k,\alpha}$ be its coefficients in this basis. On the independent Gaussian product space indexed by $I$, the L² sums
--
--   $$p_k=\sum_{\operatorname{gr}(\alpha)=d_k}c_{k,\alpha}\psi_\alpha(Z)$$
--
--   exist in $H_{d_k}^{\rm gr}(Z)$, and $(p_{n,k})_{k\in\mathbb N}\Rightarrow_U(p_k)_{k\in\mathbb N}$ in the product topology. This includes arbitrary, potentially uncountable primitive index sets, all degrees including zero, and the whole countable family jointly. It is the structural regularity theorem behind finite approximation.
--
--   Differences from the source:
--   - encoding: the homogeneous quotient and its Hermite orthonormal basis → bounded representative sequences, ultralimit pairings, homogeneous membership modulo norm-null sequences, and finite-span density; reason: these express membership and the orthonormal-basis property on representatives without an assumed whole-chaos basis
--   - reading: I is written as the disjoint union of I_d over natural d, while §2 requires strictly positive grades → an arbitrary index set graded by positive natural numbers, with each grade fiber a primitive basis; reason: including grade zero would admit e=±1 and ψ₂(e)=0, contradicting orthonormality; follows the standing convention in §2
--   - generalization: representatives normalized to E e²_{n,i}=1 exactly → normalization for U-almost every n; reason: the stronger source hypothesis implies this one; n=0 has no nonzero positive-degree chaos, and changing U-small sets changes no class
--   - encoding: basis coefficient expansions and joint convergence of the countable family → coefficients computed as ultralimits, existence of L² sums through finite-partial-sum nets, and TendstoInDistribution on ℕ → ℝ along U; reason: nets accommodate uncountable I without a pointwise-series assumption and retain the full product-topology convergence
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), Theorem 3.5, p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

theorem theorem_3_5 {I : Type*} (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (g : I → ℕ) (e : I → Sequence)
    (he : PrimitiveBasis U g e) :
    (∀ d : ℕ, HermiteUltraBasis U g e d) ∧
    (∀ (d : ℕ → ℕ) (p : ℕ → Sequence) (hp : ∀ k, boundedHom (d k) (p k)),
      ∃ P : ℕ → GaussianL2 I,
        (∀ k, HasGradedExpansion g (d k) (ultraCoefficient U e (p k)) (P k)) ∧
        TendstoInDistribution (fun n x k => p k n x) (U : Filter ℕ)
          (fun x k => P k x) (fun _ => gaussianProduct ℕ) (gaussianProduct I)) := by sorry

end GaussPolyReg.Approx
