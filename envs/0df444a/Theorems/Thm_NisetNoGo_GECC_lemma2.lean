-- Prove2me | Theorems.Thm_NisetNoGo_GECC_lemma2
-- name    : NisetNoGo.GECC.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:16.016038+00:00
-- url     : https://prove2.me/theorems/dc455e76-87be-4aa8-a2da-3c66472a8dc3
-- title:
--   Lemma 2, (5), (9) — entanglement degradation determines output negativity
-- statement:
--   Let $T=(M,N)$ be a completely positive single-mode Gaussian channel, and let $\nu_-(r)$ and $E_N(r)$ be the smallest partially transposed symplectic eigenvalue and logarithmic negativity after $T$ acts on one half of a two-mode squeezed vacuum. With $D[T]$ the entanglement degradation,
--
--   $$\min\{\nu_-(r)^2,1\}\longrightarrow D[T]\qquad(r\to\infty).$$
--
--   If $\det N>0$, then also
--
--   $$E_N(r)\longrightarrow-\tfrac12\log D[T].$$
--
--   The first limit characterizes degradation for all channel determinant classes. The second gives the paper's logarithmic-negativity formula on its finite-value domain.
--
--   **Formalization Note** At $\det N=0$, complete positivity forces $D[T]=0$ and the limiting negativity is infinite; Lean's real logarithm of zero would give an incorrect finite value. The paper's infinite-squeezing state is represented by limits of finite-$r$ quantities.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, pp. 2–3, Lemma 2, (5), (9)

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13
open Filter

namespace NisetNoGo.GECC

theorem lemma2
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N) :
    Tendsto (fun r : ℝ => min (lambdaMin (gammaOut M N r) ^ 2) 1)
      atTop (nhds (entDeg M N)) ∧
    (0 < N.det → Tendsto (fun r : ℝ => logNeg (gammaOut M N r))
      atTop (nhds (-(1 / 2 : ℝ) * Real.log (entDeg M N)))) := by sorry

end NisetNoGo.GECC
