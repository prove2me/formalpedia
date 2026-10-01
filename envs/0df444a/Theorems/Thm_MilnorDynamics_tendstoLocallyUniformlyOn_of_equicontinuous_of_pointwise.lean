-- Prove2me | Theorems.Thm_MilnorDynamics_tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise
-- name    : MilnorDynamics.tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:57:51.878297+00:00
-- url     : https://prove2.me/theorems/b6c03c10-76de-4991-928e-d5ee82c9319e
-- title:
--   Pointwise convergence of a uniformly equicontinuous family is locally uniform
-- statement:
--   **Pointwise convergence plus uniform equicontinuity gives locally uniform convergence.** Let $U\subseteq\mathbb C$ be open, let $f_n$ be uniformly equicontinuous on every compact subset of $U$ with a modulus uniform in $n$, let $g$ be continuous on $U$, and suppose $f_n(x)\to g(x)$ for every $x\in U$. Then $f_n\to g$ locally uniformly on $U$.
--
--   Proof. Fix a compact $K\subseteq U$ and $\varepsilon>0$. Equicontinuity gives $\delta_1$ with $|f_n(x)-f_n(y)|<\varepsilon/3$ whenever $|x-y|<\delta_1$, and Heine-Cantor applied to the continuous $g$ on the compact $K$ gives $\delta_2$ with $|g(x)-g(y)|<\varepsilon/3$ whenever $|x-y|<\delta_2$. With $\delta=\min(\delta_1,\delta_2)$, compactness of $K$ yields finitely many points of $K$ whose $\delta/2$-balls cover $K$; at those finitely many points the pointwise convergence holds eventually, and a finite intersection of eventual statements is eventual. Beyond that stage, for any $y\in K$ and a centre $x$ with $|y-x|<\delta/2$,
--   $$|f_n(y)-g(y)|\le|f_n(y)-f_n(x)|+|f_n(x)-g(x)|+|g(x)-g(y)|<\varepsilon .$$
--   Since $K$ was an arbitrary compact subset of $U$, this is local uniform convergence.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the standard equicontinuity upgrade inside the Arzela-Ascoli proof.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem tendstoLocallyUniformlyOn_of_equicontinuous_of_pointwise (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε)
    (hcont : ContinuousOn g U)
    (hpt : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    TendstoLocallyUniformlyOn f g atTop U := by sorry

end MilnorDynamics
