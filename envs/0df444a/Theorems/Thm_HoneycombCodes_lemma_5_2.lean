-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_5_2
-- name    : HoneycombCodes.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:38.50889+00:00
-- url     : https://prove2.me/theorems/a8d671d0-e61a-46eb-a01b-94a119bf4e16
-- title:
--   Lemma 5.2 — strict-interior approximation of $D_{HC}$
-- statement:
--   Every point of $D_{HC}$ in (3)–(6) is a limit of points satisfying the strict conditions (49). Moreover, if $q\in D_{HC}$ and $\Gamma_{HC}(q)>s$, then there are strict-interior points $q_r\to q$ with $\Gamma_{HC}(q_r)>s$ and $\Phi_{HC}(q_r)\to\Phi_{HC}(q)$.
--
--   This lets the soundness argument, which needs strict-interior points, reach every point of the variational problem (9).
--
--   **Formalization Note** Sequences are given coordinatewise; $s$ is an arbitrary real number.
--
--   Differences from the source:
--
--   - encoding: points q_r → q in ℝ⁴ → four coordinate sequences, each converging to the corresponding coordinate of q; reason: convergence in ℝ⁴ is coordinatewise convergence
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §5.1, Lemma 5.2, p.26 (PDF 28)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC

set_option autoImplicit false

open Filter Topology

namespace HoneycombCodes

/-- **Lemma 5.2**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.26 (PDF 28). Every point of `D_HC` in (3)–(6) is a limit of points
satisfying (49). Moreover, if `q ∈ D_HC` and `Γ_HC(q) > s`, then there are strict-interior
points `q_r → q` with `Γ_HC(q_r) > s` and `Φ_HC(q_r) → Φ_HC(q)`.

**Formalization Note.** A point is a quadruple of reals; a sequence `q_r` is given by its four
coordinate sequences, and `q_r → q` is coordinatewise convergence. `s` is an arbitrary real. -/
theorem lemma_5_2 :
    (∀ x η ρ z : ℝ, InDHC x η ρ z →
      ∃ xs ηs ρs zs : ℕ → ℝ, (∀ r, InStrictHC (xs r) (ηs r) (ρs r) (zs r)) ∧
        Tendsto xs atTop (𝓝 x) ∧ Tendsto ηs atTop (𝓝 η) ∧ Tendsto ρs atTop (𝓝 ρ) ∧
        Tendsto zs atTop (𝓝 z)) ∧
    (∀ s x η ρ z : ℝ, InDHC x η ρ z → s < GammaHC x η ρ z →
      ∃ xs ηs ρs zs : ℕ → ℝ, (∀ r, InStrictHC (xs r) (ηs r) (ρs r) (zs r)) ∧
        Tendsto xs atTop (𝓝 x) ∧ Tendsto ηs atTop (𝓝 η) ∧ Tendsto ρs atTop (𝓝 ρ) ∧
        Tendsto zs atTop (𝓝 z) ∧
        (∀ r, s < GammaHC (xs r) (ηs r) (ρs r) (zs r)) ∧
        Tendsto (fun r => PhiHC (xs r) (ηs r) (ρs r) (zs r)) atTop (𝓝 (PhiHC x η ρ z))) := by sorry

end HoneycombCodes
