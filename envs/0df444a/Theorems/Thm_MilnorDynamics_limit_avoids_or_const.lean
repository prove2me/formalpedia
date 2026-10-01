-- Prove2me | Theorems.Thm_MilnorDynamics_limit_avoids_or_const
-- name    : MilnorDynamics.limit_avoids_or_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:40:57.053403+00:00
-- url     : https://prove2.me/theorems/ab676358-bd21-4a1f-945f-c8c2eb4c4f6e
-- title:
--   Hurwitz for limits - a locally uniform limit of maps avoiding one value avoids it or is constant
-- statement:
--   **Hurwitz's theorem for limits.** Let $U\subseteq\mathbb C$ be a domain, let $f_n:\mathbb C\to\mathbb C$ be holomorphic on $U$ and never equal to $c$ on $U$, and suppose $f_n$ converges to $g$ locally uniformly on $U$, with $g$ continuous. Then either $g$ never takes the value $c$ on $U$, or $g$ is identically $c$ on $U$:
--
--   $$\Bigl(\forall z\in U,\ g(z)\neq c\Bigr)\quad\text{or}\quad\Bigl(\forall z\in U,\ g(z)=c\Bigr).$$
--
--   In other words the set $\mathbb C\setminus\{c\}$ is closed under locally uniform limits along holomorphic maps on a connected open set: a limit cannot cross the value $c$ at isolated points, it must either stay away from $c$ or collapse to $c$ everywhere.
--
--   This is the analytic half of the dichotomy used for the normalised core of Milnor's Theorem 3.7. Applied with $c=0$ and $c=1$, it shows that a locally uniform limit of a holomorphic family omitting $0$ and $1$ either avoids both values or is the constant $0$ or the constant $1$; the constant cases are then handled by the purely metric lemma that such a family diverges locally uniformly from $\mathbb C\setminus\{0,1\}$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (normal families and Hurwitz's theorem); the statement is the classical Hurwitz theorem that a locally uniform limit of zero-free holomorphic functions on a domain is either zero-free or identically zero, applied to $f_n - c$.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem limit_avoids_or_const (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ) (c : ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({c}ᶜ : Set ℂ))
    (g : ℂ → ℂ) (hg : ContinuousOn g U)
    (hc : TendstoLocallyUniformlyOn f g atTop U) :
    (∀ z ∈ U, g z ≠ c) ∨ (∀ z ∈ U, g z = c) := by sorry

end MilnorDynamics
