-- Prove2me | Theorems.Thm_HairerSPDE_map_add_null_iff
-- name    : HairerSPDE.map_add_null_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T10:25:04.670145+00:00
-- url     : https://prove2.me/theorems/99c743c4-fc78-431b-84a5-acfff71bf183
-- title:
--   Cameron-Martin quasi-invariance: finite-norm translates preserve null sets
-- statement:
--   **Cameron–Martin quasi-invariance (correct null-set form).** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$ a point of finite Cameron–Martin norm, $\|h\|_\mu \neq \infty$. Write $T_h(x) = x + h$ and $(T_h)_*\mu$ for the push-forward of $\mu$. Then $\mu$ and $(T_h)_*\mu$ have exactly the same null sets: for every Borel set $A \subseteq B$,
--
--   $$ (T_h)_*\mu(A) = 0 \quad \Longleftrightarrow \quad \mu(A) = 0 . $$
--
--   Equivalently, $\mu(A) = 1$ if and only if $(T_h)_*\mu(A) = 1$. This is the form of the Cameron–Martin theorem used in Proposition 4.45 of Hairer's notes: translating a full-measure Borel set by a Cameron–Martin vector again yields a full-measure set. It is strictly weaker than the false statement $(T_h)_*\mu = \mu$ (a non-degenerate centred Gaussian is never translation invariant; $\mathcal N(0,1)$ shifted by $h \neq 0$ is $\mathcal N(h,1)$). It is strictly stronger than mere absolute continuity in one direction: because the density is strictly positive, the two measures are in fact equivalent.
--
--   The proof is the explicit density formula (4.14) together with the definition of the Cameron–Martin norm. For $h$ in the Cameron–Martin space there is a representer $h^{*} \in B^{*}$ with $C_\mu(h^{*}, \ell) = \ell(h)$ for all $\ell \in B^{*}$ and $C_\mu(h^{*},h^{*}) = \|h\|_\mu^{2} < \infty$, and then
--
--   $$ (T_h)_*\mu = \exp\!\Bigl(h^{*}(x) - \tfrac12 \|h\|_\mu^{2}\Bigr)\,\mu . $$
--
--   The density is everywhere strictly positive, so it vanishes exactly on $\mu$-null sets; hence $(T_h)_*\mu(A) = 0$ iff $\mu(A) = 0$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Section 4.2 (Cameron-Martin theorem) and equation (4.14), used for Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem map_add_null_iff {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∀ A : Set B, MeasurableSet A → ((μ.map (fun x : B => x + h)) A = 0 ↔ μ A = 0) := by sorry

end HairerSPDE
