-- Prove2me | Theorems.Thm_FunctionalIto_Formula_lemma_2_6
-- name    : FunctionalIto.Formula.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:32.280931+00:00
-- url     : https://prove2.me/theorems/85e11120-e0bf-41f0-9301-76cf46380d7d
-- title:
--   Lemma 2.6, p. 6 — pathwise regularity: t ↦ F_t(x_{t−}, v_{t−}) is left-continuous for F ∈ ℂ_l^{0,0}
-- statement:
--   Let $F$ be a nonanticipative functional (in the sense of Definition 2.1) in $\mathbb C^{0,0}_l([0,T))$, and let $(x,v)\in D([0,T],\mathbb R^d)\times\mathcal S_T$. Then the real path
--   $$t\longmapsto F_t(x_{t-},v_{t-})$$
--   is left-continuous at every $t\in(0,T)$. Here $x_{t-}$ is the path equal to $x$ on $[0,t)$ and to the left limit $x(t-)$ at $t$.
--
--   Composing a left-continuous functional with cadlag paths thus yields left-continuous processes; this gives the predictability of $F_t(X_t,A_t)$ (Theorem 2.7) and the left-continuity of the map $\psi$ in the proof of Theorem 4.1.
--
--   **Formalization Note.** Left-continuity at $t$ is continuity within $[0,t)$. The paper defines $F$ on $[0,T)$ only, so the statement concerns $t<T$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, p. 6, Lemma 2.6

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace FunctionalIto.Formula

/-- Lemma 2.6 (p. 6), pathwise regularity: if `F ∈ ℂ_l^{0,0}([0,T))`, then for every
`(x, v) ∈ D([0,T], ℝ^d) × 𝒮_T` the path `t ↦ F_t(x_{t−}, v_{t−})` is left-continuous at every
`t ∈ (0,T)`. -/
theorem lemma_2_6 {d : ℕ} (T : ℝ≥0) (F : Functional d ℝ) (hFna : IsNonanticipative F)
    (hFm : IsCanonicallyMeasurable T F) (hF : LeftContinuous T F)
    (x : Path d) (v : MPath d) (hxv : Admissible T x v) (t : ℝ≥0) (ht0 : 0 < t) (htT : t < T) :
    ContinuousWithinAt (fun s => F s (leftStop s x) (leftStop s v)) (Set.Iio t) t := by sorry

end FunctionalIto.Formula
