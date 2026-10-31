-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_167
-- name    : FuchsThesis.Holevo.eq_3_167
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:50.329006+00:00
-- url     : https://prove2.me/theorems/2d79fb1f-3835-4ebd-8c1e-138f67b2dad9
-- title:
--   Eq. (3.167): Holevo's intermediate bound $I(t)\le L(t)\le S(t)$
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional Hilbert space, forming a binary quantum channel with priors $\pi_0=1-t$, $\pi_1=t$. Write $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$, $\hat\Delta=\hat\rho_1-\hat\rho_0$, and let $\mathcal L_{\hat\rho}$ be the super-operator (3.181). Let $L$ be the function defined by
--
--   $$
--   L''(t) = -\mathrm{tr}\big(\hat\Delta\,\mathcal L_{\hat\rho}(\hat\Delta)\big)\ \ (0<t<1), \qquad L(0)=L(1)=0 .
--   $$
--
--   Then such an $L$ exists, and for every $0\le t\le1$
--
--   $$
--   I(t) \;\le\; L(t) \;\le\; S(t),
--   $$
--
--   where $I(t)$ is the accessible information (3.146), the mutual information maximized over all measurements, and $S(t)=S(\hat\rho)-(1-t)S(\hat\rho_0)-tS(\hat\rho_1)$ is the Holevo quantity (3.149), all in nats.
--
--   The outer inequality is the Holevo bound; $L$ is the intermediate function whose existence Holevo's original proof required, here given explicitly through $\mathcal L_{\hat\rho}$.
--
--   **Formalization Note** "$L$ is the function with this second derivative and these boundary values" is the predicate `IsIntermediateL` (continuous on $[0,1]$, twice differentiable on $(0,1)$ with the given second derivative, zero at $0$ and $1$). The theorem asserts that such an $L$ exists and that every such $L$ (it is unique) lies between $I$ and $S$ on $[0,1]$. No invertibility of $\hat\rho_0,\hat\rho_1$ is assumed.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - encoding: L defined by its second derivative (3.187) and the boundary condition (3.166) → (∃ L, IsIntermediateL ρ0 ρ1 L) ∧ ∀ L, IsIntermediateL ρ0 ρ1 L → bounds on [0, 1]; reason: the defining conditions determine L uniquely, so 'the' L exists and satisfies the bounds
--   - reading: L″(t) = −tr(Δ̂𝓛_ρ̂(Δ̂)) with L(0) = L(1) = 0 (no regularity stated) → L continuous on [0, 1], twice differentiable on (0, 1) with that second derivative there; reason: tr(Δ̂𝓛_ρ̂(Δ̂)) can be unbounded as t → 0 or 1 (ρ0 = |0⟩⟨0|, ρ1 = 1/2 on a qubit gives a term 1/(2t)), so the ODE holds on the open interval; continuity at the endpoints makes the boundary condition meaningful
--   - encoding: max over measurements {Ê_b} in I(t) → sSup over every POVM E : Fin m → Matrix d d ℂ, any m; reason: the set is nonempty and bounded above; by Davies' theorem the maximum is attained
--   - encoding: tr(Δ̂𝓛_ρ̂(Δ̂)) → its real part; reason: the trace is real for 0 < t < 1
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.167) with (3.165)–(3.166), pp.67–68 (PDF pp.76–77); definition (3.187), p.71 (PDF p.80)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_accessibleInfo
import Definitions.Def_FuchsThesis_Holevo_holevoS
import Definitions.Def_FuchsThesis_Holevo_IsIntermediateL

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.167) with (3.165)–(3.166), pp.67–68
(PDF pp.76–77), and the definition (3.187) of `L″`, p.71 (PDF p.80): for density operators
`ρ̂0, ρ̂1` on a finite-dimensional space, the function `L` with
`L″(t) = −tr(Δ̂ 𝓛_ρ̂(Δ̂))` on `(0, 1)` and `L(0) = L(1) = 0` exists, and for every `t ∈ [0, 1]`
`I(t) ≤ L(t) ≤ S(t)`,
where `I(t)` is the accessible information (3.146) (supremum of the mutual information over every
POVM) and `S(t)` the Holevo quantity (3.149), both in nats.

**Formalization Note.** `IsIntermediateL ρ0 ρ1 L` encodes the source's characterization of `L`
(continuous on `[0, 1]`, twice differentiable on `(0, 1)` with the second derivative (3.187),
boundary values (3.166)). The statement asserts that such an `L` exists and that every such `L`
(it is unique) lies between `I` and `S` on `[0, 1]`. -/
theorem eq_3_167 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1) :
    (∃ L : ℝ → ℝ, IsIntermediateL ρ0 ρ1 L) ∧
      ∀ L : ℝ → ℝ, IsIntermediateL ρ0 ρ1 L → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        accessibleInfo ρ0 ρ1 t ≤ L t ∧ L t ≤ holevoS ρ0 ρ1 t := by sorry

end FuchsThesis.Holevo
