-- Prove2me | Theorems.Thm_MilnorDynamics_either_limit_avoids_or_diverges
-- name    : MilnorDynamics.either_limit_avoids_or_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T17:28:36.162522+00:00
-- url     : https://prove2.me/theorems/da5d88b1-2812-4275-a558-01f21a4f9c02
-- title:
--   Hurwitz dichotomy — a locally uniform limit either avoids {0,1} or the sequence diverges from it
-- statement:
--   **Hurwitz's dichotomy for a two-punctured plane.** Let $U\subseteq\mathbb C$ be a connected open set, let $f_n:U\to\mathbb C\setminus\{0,1\}$ be holomorphic maps, and suppose $f_n$ converges locally uniformly on $U$ to a continuous $g:U\to\mathbb C$. Then **either** $g(U)\subseteq\mathbb C\setminus\{0,1\}$, **or** the sequence $(f_n)$ diverges locally uniformly from $\mathbb C\setminus\{0,1\}$ in the sense that for every compact $K\subseteq U$ and every compact $K'\subseteq\mathbb C\setminus\{0,1\}$ one has $f_n(K)\cap K'=\emptyset$ for all sufficiently large $n$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, p. 34 (Hurwitz argument in the proof of Corollary 3.3); Hurwitz's theorem, Handbook of Complex Analysis, compact-target form

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem either_limit_avoids_or_diverges (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (g : ℂ → ℂ) (hg : ContinuousOn g U)
    (hc : TendstoLocallyUniformlyOn f g atTop U) :
    MapsTo g U ({0, 1}ᶜ : Set ℂ) ∨
      DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
