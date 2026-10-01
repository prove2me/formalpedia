-- Prove2me | Theorems.Thm_MilnorDynamics_escapes_on_compacts_implies_diverges
-- name    : MilnorDynamics.escapes_on_compacts_implies_diverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T03:39:11.776982+00:00
-- url     : https://prove2.me/theorems/3e24e35f-8056-429f-b381-b1f87b1698be
-- title:
--   Uniform escape on compacta implies divergence from the twice-punctured plane
-- statement:
--   **From uniform escape to divergence.** Let $U\subseteq\mathbb C$ be open and let $f_n:U\to\mathbb C$ be a sequence of functions whose moduli escape uniformly on compacta: for every compact $K\subseteq U$ and every real $R$ there is $N$ with $|f_n(z)|>R$ for all $n\ge N$ and all $z\in K$. Then $(f_n)$ diverges locally uniformly from the twice-punctured plane $\mathbb C\setminus\{0,1\}$: for every compact $K\subseteq U$ and every compact $K'\subseteq\mathbb C\setminus\{0,1\}$ the sets $f_n(K)$ and $K'$ are disjoint for all sufficiently large $n$.
--
--   Proof. A compact $K'\subseteq\mathbb C\setminus\{0,1\}$ is bounded, so it lies in a closed ball about any of its points; escape past the radius of that ball plus the norm of the centre excludes it. This is the elementary metric bridge that converts the real-valued escape statement into the divergence notion used by the project's normal-family definitions; it is the exact mirror image of the bridge from a locally uniform limit to the constant punctures.
--
--   **Formalization Note** The differentiability hypothesis is carried only so that the statement slots directly into the parent's context; the proof does not use it.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem escapes_on_compacts_implies_diverges (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hesc : ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, R < ‖f n z‖) :
    DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
