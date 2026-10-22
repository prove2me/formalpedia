-- Prove2me | Theorems.Thm_JHolomorphic_contDiff_of_hasWeakPartialsOn_univ
-- name    : JHolomorphic.contDiff_of_hasWeakPartialsOn_univ
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T21:37:19.573663+00:00
-- url     : https://prove2.me/theorems/3da665be-524c-4a86-bf41-c52eba367fc3
-- title:
--   A continuous map on $\mathbb{C}$ with compactly supported $W^{1,p}$ weak partial derivatives, $p>2$, is $C^1$
-- statement:
--   Let $p>2$ and let $E$ be a finite-dimensional real normed space. Let $v:\mathbb{C}\to E$ be continuous, and suppose $v_s,v_t:\mathbb{C}\to E$ are weak partial derivatives of $v$ on all of $\mathbb{C}$ such that:
--   - $v_s$ and $v_t$ have compact support and lie in $L^p(\mathbb{C})$;
--   - $v_s$ has weak partial derivatives $v_{ss},v_{st}$ on $\mathbb{C}$, and $v_t$ has weak partial derivatives $v_{ts},v_{tt}$ on $\mathbb{C}$, all four in $L^p(\mathbb{C})$.
--
--   Then $v$ is continuously differentiable on $\mathbb{C}$. This is the global, compactly supported form of the statement that $W^{2,p}$ maps in dimension two are $C^1$.
--
--   **Formalization Note** Weak partials on $\mathbb{C}$ are `HasWeakPartialsOn Set.univ`; $L^p$ membership is `MemLp _ (ENNReal.ofReal p) volume`; compact support is `HasCompactSupport`; the conclusion is `ContDiff ℝ 1 v`. No support or integrability condition on $v$ itself is assumed beyond continuity.
-- source:
--   Standard; cf. L. C. Evans, Partial Differential Equations, §5.6.2-5.6.3; D. McDuff, D. Salamon, J-holomorphic Curves and Symplectic Topology, Appendix B.1; C. Wendl, Lectures on Symplectic Field Theory, Lecture 2

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory

/-- Let `p > 2`. If `v : ℂ → E` is continuous and has weak partial derivatives `vₛ`, `vₜ` on `ℂ`
which have compact support, lie in `L^p(ℂ)` and themselves have weak partial derivatives on `ℂ`
in `L^p(ℂ)`, then `v` is `C¹`. -/
theorem contDiff_of_hasWeakPartialsOn_univ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    {v vs vt vss vst vts vtt : ℂ → E} (hv : Continuous v)
    (hvsc : HasCompactSupport vs) (hvtc : HasCompactSupport vt)
    (h1 : HasWeakPartialsOn Set.univ v vs vt) (h2 : HasWeakPartialsOn Set.univ vs vss vst)
    (h3 : HasWeakPartialsOn Set.univ vt vts vtt)
    (hs : MemLp vs (ENNReal.ofReal p) volume) (ht : MemLp vt (ENNReal.ofReal p) volume)
    (hss : MemLp vss (ENNReal.ofReal p) volume) (hst : MemLp vst (ENNReal.ofReal p) volume)
    (hts : MemLp vts (ENNReal.ofReal p) volume) (htt : MemLp vtt (ENNReal.ofReal p) volume) :
    ContDiff ℝ 1 v := by
  sorry

end JHolomorphic
