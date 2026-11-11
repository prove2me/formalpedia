-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_eta0_pos
-- name    : FracColorLocal.KrFree.eta0_pos
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:23.117863+00:00
-- url     : https://prove2.me/theorems/2bce0dd5-0fa7-4471-9adb-4d7660ba791d
-- title:
--   §3 — (d+1)f(d)/log(d+2) is continuous and positive on [0, ∞), tends to 1, and its infimum η₀ is positive
-- statement:
--   Let $f$ be Shearer's function. The function
--
--   $$d\ \mapsto\ \frac{(d+1)f(d)}{\log(d+2)}\qquad(d\ge0)$$
--
--   is continuous and positive on $[0,\infty)$ and tends to one as $d\to\infty$, so its infimum $\eta_0$ on $[0,\infty)$ is positive. Hence $f(d)\ge\eta_0\log(d+2)/(d+1)$ for all $d\ge0$, which converts Corollary 1.8 with $s\equiv1$ into Theorem 1.5 with $\kappa=\kappa_1\eta_0$.
--
--   Differences from the source:
--   - encoding: the infimum $\eta_0$ → real `sInf` of the image of $[0,\infty)$; reason: the set is nonempty and bounded below by $0$, so `sInf` is the infimum.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 16 (PDF 17), §3, proof of Corollary 1.8 and Theorem 1.5

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Shearer

open Filter Topology

namespace FracColorLocal.KrFree

/-- §3, deduction of Theorem 1.5: `(d+1) f(d) / log(d+2)` is continuous and positive on `[0, ∞)`,
tends to one at infinity, and its infimum `η₀` on `[0, ∞)` is positive. -/
theorem eta0_pos :
    ContinuousOn (fun d : ℝ => (d + 1) * shearerF d / Real.log (d + 2)) (Set.Ici 0) ∧
    (∀ d : ℝ, 0 ≤ d → 0 < (d + 1) * shearerF d / Real.log (d + 2)) ∧
    Tendsto (fun d : ℝ => (d + 1) * shearerF d / Real.log (d + 2)) atTop (𝓝 1) ∧
    0 < sInf ((fun d : ℝ => (d + 1) * shearerF d / Real.log (d + 2)) '' Set.Ici 0) := by sorry

end FracColorLocal.KrFree
