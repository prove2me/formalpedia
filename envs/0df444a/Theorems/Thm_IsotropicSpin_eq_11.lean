-- Prove2me | Theorems.Thm_IsotropicSpin_eq_11
-- name    : IsotropicSpin.eq_11
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T04:24:56.4663+00:00
-- url     : https://prove2.me/theorems/cc1d3077-d2ca-4c40-a579-3c771e52f2b8
-- title:
--   Eqs. (11)–(12) — $\Lambda_{1/2}(\rho)=(\operatorname{tr}\rho)\tfrac13\mathbf 1+\tfrac13T\rho T^\dagger$
-- statement:
--   Let $\Lambda_{1/2}$ be the isotropic channel (6) for spin $1/2$ ($S_k=\tfrac12\sigma_k$) and $T$ the antiunitary time-reversal map $T|{+}1/2\rangle=|{-}1/2\rangle$, $T|{-}1/2\rangle=-|{+}1/2\rangle$ (12). For every Hermitian $2\times2$ matrix $\rho$,
--
--   $$
--   \Lambda_{1/2}(\rho)=(\operatorname{tr}\rho)\,\frac13\,\mathbf 1+\frac13\,T\rho T^\dagger .
--   $$
--
--   This closed form shows that $\Lambda_{1/2}$ maps every pure state to a matrix with spectrum $(1/3,2/3)$.
--
--   **Formalization Note** $T\rho T^\dagger$ is `timeReversal ρ` $=J\bar\rho J^\dagger$. The identity is not stated for non-Hermitian $\rho$: the left side is linear and the right side conjugate-linear in $\rho$.
--
--   Differences from the source:
--   - generalization: ρ a density matrix → every Hermitian ρ; reason: the identity holds for all Hermitian ρ; specializes to density matrices
--   - encoding: T antiunitary with T|+1/2⟩ = |−1/2⟩, T|−1/2⟩ = −|+1/2⟩ → TρT† written as J ρ̄ J† with J = !![0, -1; 1, 0] and ρ̄ the entrywise conjugate; reason: T = J∘(complex conjugation) in the basis (|+1/2⟩, |−1/2⟩); same operator
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eqs. (11)–(12), p.2

import Mathlib
import Definitions.Def_IsotropicSpin_spinHalf
import Definitions.Def_IsotropicSpin_isotropicChannel
import Definitions.Def_IsotropicSpin_timeReversal

open scoped Matrix

namespace IsotropicSpin

/-- **The time-reversal form of `Λ_{1/2}`**, Alicki, arXiv:quant-ph/0402080v1, eqs. (11)–(12),
p. 2: `Λ_{1/2}(ρ) = (tr ρ) (1/3) 𝟙 + (1/3) T ρ T†`, with `T` the antiunitary time-reversal map
`T|+1/2⟩ = |−1/2⟩`, `T|−1/2⟩ = −|+1/2⟩` (`timeReversal ρ = T ρ T†`).

**Formalization Note** Stated for every Hermitian `ρ` (the paper's `ρ` is a density matrix). It is
not stated for all matrices: `ρ ↦ T ρ T†` is conjugate-linear (T is antiunitary) while `Λ_{1/2}`
is linear, so (11) fails for non-Hermitian `ρ`. -/
theorem eq_11 (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.IsHermitian) :
    isotropicChannel (1 / 2) spinHalf ρ =
      (ρ.trace / 3) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 / 3 : ℂ) • timeReversal ρ := by sorry

end IsotropicSpin
