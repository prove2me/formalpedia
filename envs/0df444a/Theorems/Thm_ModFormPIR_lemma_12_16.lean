-- Prove2me | Theorems.Thm_ModFormPIR_lemma_12_16
-- name    : ModFormPIR.lemma_12_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:31.741521+00:00
-- url     : https://prove2.me/theorems/79385d26-eae9-4845-ab4d-52dee543ab6a
-- title:
--   Lemma 12.16, p.70 — the transformation law of $\Theta$ under $SL_2(\mathbb Z)$
-- statement:
--   For any $g=\begin{pmatrix}a&b\\c&d_0\end{pmatrix}\in SL_2(\mathbb Z)$, as functions of $(\tau,w)\in\mathbb H\times\mathbb C$,
--   $$\Theta(g*(\tau,w))\propto_\zeta G(g,\tau)^{1/2}\exp\Big(\frac{\pi iqcw^2}{G(g,\tau)}\Big)\rho(g)\Theta(\tau,w),$$
--   where $G(g,\tau)^{1/2}$ is any holomorphic branch of the square root of $\tau\mapsto G(g,\tau)$ and $\rho$ is the Weil representation with $\mu=(q+1)/2$.
--
--   All modularity in the proof descends from this law.
--
--   Differences from the source:
--   - encoding: ∝_ζ, "any holomorphic branch" → for every holomorphic r with r² = G(g,·) there is one root of unity u, for all τ, w; reason: the definition of ∝_ζ, p.43
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 12.16, p.70 (PDF p.74), with Definitions 12.10, 12.12, pp.68–69

import Mathlib
import Definitions.Def_ModFormPIR_CharForms

open Complex Matrix
open scoped MatrixGroups UpperHalfPlane Real

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 12.16**, p.70, (47). Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For `g = [a b; c d₀] ∈ SL₂(ℤ)`, as functions of `(τ,w)`: `Θ(g∗(τ,w)) ∝_ζ G(g,τ)^{1/2} exp(πiqcw²/G(g,τ)) ρ(g)Θ(τ,w)`, for any holomorphic branch of the square root.

**Formalization Note.** `∝_ζ`: one root of unity `u`, for all `τ, w`, per `g` and per branch `r`. `μ = (q+1)/2`. `g∗(τ,w) = (g∗τ, w/G(g,τ))` (Definition 12.10). -/
theorem lemma_12_16 (q : ℕ) [Fact q.Prime] (hodd : Odd q)
    (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (hρ : IsWeil q (muHalf q) ρ) (g : SL(2, ℤ))
    (r : ℍ → ℂ) (hr : IsHolo r) (hr2 : ∀ τ, r τ ^ 2 = denomG g τ) :
    ∃ u : ℂ, (∃ n : ℕ, 0 < n ∧ u ^ n = 1) ∧ ∀ (τ : ℍ) (w : ℂ),
      Theta q (g • τ) (w / denomG g τ) =
        (u * r τ * exp (π * I * q * ((g 1 0 : ℤ) : ℂ) * w ^ 2 / denomG g τ)) •
          (ρ g).mulVec (Theta q τ w) := by sorry

end ModFormPIR
