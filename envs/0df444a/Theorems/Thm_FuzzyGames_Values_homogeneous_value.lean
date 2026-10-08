-- Prove2me | Theorems.Thm_FuzzyGames_Values_homogeneous_value
-- name    : FuzzyGames.Values.homogeneous_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:08.820507+00:00
-- url     : https://prove2.me/theorems/b5f7535c-03e5-4dd9-af20-d03f7c0589e8
-- title:
--   Theorem 8.1, proof — for positively homogeneous v, Dv(tτ^N) = Dv(τ^N) and (4) becomes ψ_n v = Dv(τ^N)
-- statement:
--   Let $v\in V^n$ be positively homogeneous on the orthant: $v(t\tau)=t\,v(\tau)$ for all $t>0$ and $\tau\in\mathbb R^n_+$. Then
--
--   1. $Dv(t\tau^N)=Dv(\tau^N)$ for every $t>0$;
--   2. the diagonal formula (4) reduces to the gradient at the full coalition:
--   $$(\psi_n v)_i=\int_0^1\frac{\partial v}{\partial\tau_i}(t\tau^N)\,dt=\frac{\partial v}{\partial\tau_i}(\tau^N).$$
--
--   Combined with Proposition 2.1, this identifies $\psi_n v$ with the unique element of the core when $v$ is moreover concave.
--
--   **Formalization Note** $Dv$ is the Fréchet derivative of the ($C^1$ on $\mathbb R^n$) function $v$; $\tau^N=(1,\dots,1)$ is interior to the orthant, so it is determined by the values of $v$ on $\mathbb R^n_+$. Homogeneity is required on the orthant, as in §2 (1)–(2), where the paper extends $v$ from the cube to $\mathbb R^n_+$.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8, proof of Theorem 8.1, p. 11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

namespace FuzzyGames.Values

/-- §8, proof of Theorem 8.1 (p. 11): if `v ∈ V^n` is positively homogeneous on `ℝ^n_+`, then
`Dv(tτ^N) = Dv(τ^N)` for every `t > 0`, and (4) becomes `ψ_n v = Dv(τ^N)`. -/
theorem homogeneous_value (n : ℕ) (v : Vn n) (hv : IsPosHomogeneous v.1) :
    (∀ t : ℝ, 0 < t → fderiv ℝ v.1 (t • (1 : Fin n → ℝ)) = fderiv ℝ v.1 1) ∧
      diagValue v.1 = fun i => fderiv ℝ v.1 1 (Pi.single i 1) := by sorry

end FuzzyGames.Values
