-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
-- name    : LanglandsTunnell.CubicInduction.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/aa5b8965-6f9b-5840-a100-81d7b6d59028
-- title:
--   Diagonal value as e₃ᶜ times a two-row torus value
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $\mathbb{Q}_v$ for the $v$-adic completion, and let $W$ be a complex-valued function on $\mathrm{GL}_3(\mathbb{Q}_v)$ and $e_3$ a complex number. Assume: (i) $W$ is right invariant under `localMaximalCompact3`, i.e. $W(gu) = W(g)$ for all $g$ and all $u \in \mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose entries of $u^{-1}$ have valuation $\le 1$; (ii) $W(z g) = e_3 W(g)$ for all $g$, where $z$ is the central element with underlying matrix $\mathrm{diag}(\varpi,\varpi,\varpi)$, $\varpi$ the chosen uniformiser of $\mathbb{Q}_v$. Let $t \in \mathrm{GL}_3(\mathbb{Q}_v)$ and $d : \mathrm{Fin}\,3 \to \mathbb{Q}_v$ with underlying matrix of $t$ equal to $\mathrm{diag}(d_0,d_1,d_2)$, let $k_1,k_2$ be natural numbers and $c$ an integer, and assume the valuations satisfy $|d_0| = \exp(-(k_1+c))$, $|d_1| = \exp(-(k_2+c))$ and $|d_2| = \exp(-c)$ in the value group written multiplicatively via `WithZero.exp`. Then $W(t) = e_3^{\,c} \cdot W(\,\mathrm{twoRowPointLocal}\ v\ k_1\ k_2\,)$, the latter argument being the image under `iotaGL` of the $2 \times 2$ diagonal unit $\mathrm{diag}(\pi^{k_1},\pi^{k_2})$, $\pi =$ `ratPrimeUnit v`. No ordering between $k_1$ and $k_2$ is assumed.
--
--   This is the normalisation step for local Whittaker-type functions on $\mathrm{GL}_3$: right invariance under the integral maximal compact subgroup together with the central transformation law reduces a value at an arbitrary diagonal element to a value at one of the standard two-parameter torus points, up to a power of the central eigenvalue. It is used in the construction of induced spherical Whittaker functions at good places, in the vanishing criterion for coset eigenfunctions, and in the bounds on root sizes for unitary characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
    (v : HeightOneSpectrum (𝓞 ℚ)) (W : LocalGL3 v → ℂ) (e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (k₁ k₂ : ℕ) (c : ℤ)
    (h0 : Valued.v (d 0) = WithZero.exp (-((k₁ : ℤ) + c)))
    (h1 : Valued.v (d 1) = WithZero.exp (-((k₂ : ℤ) + c)))
    (h2 : Valued.v (d 2) = WithZero.exp (-c)) :
    W t = e₃ ^ c * W (twoRowPointLocal v k₁ k₂) := by sorry
