-- Prove2me | Theorems.Thm_MasulloRH_localized_edge_pole_autocorrelation_sandwich
-- name    : MasulloRH.localized_edge_pole_autocorrelation_sandwich
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T20:03:47.319291+00:00
-- url     : https://prove2.me/theorems/76a873e7-8aba-4133-87f7-a3bb08323a4c
-- title:
--   Unit normalization and finite-window bounds for the global floor-cell pole profile at arbitrary gap
-- statement:
--   Let $L,\alpha>0$ and let $\theta(x)=x-L\lfloor x/L\rfloor$. Extend the reference pole profile by zero on the negative half-line and put $g(x)=\sqrt{2\alpha}\exp(-\alpha x+\alpha(2\theta(x)-L))$ on $x\ge0$. Its nonzero set is $[0,\infty)$. Its squared mass in the first $n$ complete cells is exactly $1-e^{-2\alpha nL}$, and its total squared mass on $(0,\infty)$ is one.
--
--   For a physical upper endpoint $R\in\mathbb R$ and a nonnegative lag $s$, set $D=\max(R-s,0)$, $K=\int_0^D g(t)g(t+s)\,dt$, and $B=e^{-\alpha s}(1-e^{-2\alpha D})$. Then
--   $$e^{-2\alpha L} B\ \le K\ \le e^{2\alpha L}B.$$
--   Moreover $K=0$ precisely when $R\le s$. The bounds hold simultaneously for every real upper endpoint and every nonnegative lag, including endpoints interior to a cell.
-- source:
--   Masullo, The Music of the Primes, §§7.3.2 and 11.3.2. Original quantitative finite-window estimate for the reference pole vector described by Yi in mission comment d9bf59c5-5600-4dbe-9840-c2ca4f0e4293. Yi's theorem 9f8d3d6f-1c98-4e15-8ab8-eee4e526ae48 and MasulloRepair.pole_cell_overlap (01222299-51e8-42cb-82b6-2c24df6ddd21) previously evaluated cellwise overlaps at gap 1/2. The finite cutoff calculation for the atomic projection is 1cf19c76-703d-4111-bb8a-33c56a6910ac.

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped Topology

theorem MasulloRH.localized_edge_pole_autocorrelation_sandwich
    (L α : ℝ) (hL : 0 < L) (hα : 0 < α) :
    let θ := fun x : ℝ => x - L * (⌊x / L⌋ : ℝ)
    let g := fun x : ℝ => if 0 ≤ x then
      Real.sqrt (2 * α) * Real.exp (-α * x + α * (2 * θ x - L)) else 0
    let K := fun R s : ℝ => ∫ t in (0 : ℝ)..max (R - s) 0, g t * g (t + s)
    let B := fun R s : ℝ => Real.exp (-α * s) *
      (1 - Real.exp (-2 * α * max (R - s) 0))
    Function.support g = Ici 0 ∧
    (∀ n : ℕ, (∫ t in (0 : ℝ)..(n : ℝ)*L, (g t)^2) =
      1 - Real.exp ((-2 * α) * ((n : ℝ) * L))) ∧
    (∫ t in Ioi (0 : ℝ), (g t)^2) = 1 ∧ ∀ R s : ℝ, 0 ≤ s →
      (K R s = 0 ↔ R ≤ s) ∧
      Real.exp (-2 * α * L) * B R s ≤ K R s ∧
      K R s ≤ Real.exp (2 * α * L) * B R s := by sorry
