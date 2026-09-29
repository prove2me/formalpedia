-- Prove2me | Theorems.Thm_NeutrinoDecoherence_dissipator_pauli_expansion
-- name    : NeutrinoDecoherence.dissipator_pauli_expansion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:11:22.439053+00:00
-- url     : https://prove2.me/theorems/51e58889-9c16-4c45-b678-50f00f882964
-- title:
--   Pauli-basis form of the two-level Dissipator, eq. (3.5)
-- statement:
--   Let $a=(a_{ij})_{i,j=1}^3$ be a Hermitian complex matrix and let $D$ be the associated Dissipator
--   $$D[\rho]=\tfrac12\sum_{i,j=1}^3 a_{ij}\bigl(2\sigma_i\rho\sigma_j-\{\sigma_j\sigma_i,\rho\}\bigr).$$
--   For real $\rho_0,\rho_1,\rho_2,\rho_3$ and $\rho=\rho_0 I+\rho_1\sigma_1+\rho_2\sigma_2+\rho_3\sigma_3$,
--   $$\begin{aligned}D[\rho]={}&2\bigl(\mathrm{Re}\,a_{21}\,\rho_2+\mathrm{Re}\,a_{31}\,\rho_3-(a_{22}+a_{33})\rho_1+2\rho_0\,\mathrm{Im}\,a_{32}\bigr)\sigma_1\\&+2\bigl(\mathrm{Re}\,a_{12}\,\rho_1+\mathrm{Re}\,a_{32}\,\rho_3-(a_{11}+a_{33})\rho_2+2\rho_0\,\mathrm{Im}\,a_{13}\bigr)\sigma_2\\&+2\bigl(\mathrm{Re}\,a_{13}\,\rho_1+\mathrm{Re}\,a_{23}\,\rho_2-(a_{11}+a_{22})\rho_3+2\rho_0\,\mathrm{Im}\,a_{21}\bigr)\sigma_3.\end{aligned}$$
--
--   This is the component form from which the vectorized Dissipator (3.6) and the table of cases in Section 3.2 are read off.
--
--   **Formalization Note** The printed eq. (3.5) has $-2\rho_0\,\mathrm{Im}(\cdot)$ in the three $\rho_0$ terms. This draft uses $+2\rho_0\,\mathrm{Im}(\cdot)$, which is what the thesis' own derivation (B.8)–(B.9) gives and what a direct numerical check of definition (3.4) gave. Diagonal entries $a_{ii}$ enter through their real parts (they are real because $a$ is Hermitian).
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 3.1, p. 56, eqs. (3.4)–(3.5); Appendix B.2, pp. 118–119, eqs. (B.6)–(B.9). Sign of the Im-terms corrected, see Formalization Note.

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem dissipator_pauli_expansion (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.IsHermitian)
    (r₀ r₁ r₂ r₃ : ℝ) :
    dissipator a ((r₀ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (r₁ : ℂ) • pauli 0 +
        (r₂ : ℂ) • pauli 1 + (r₃ : ℂ) • pauli 2) =
      ((2 * ((a 1 0).re * r₂ + (a 2 0).re * r₃ - (a 1 1).re * r₁ - (a 2 2).re * r₁
          + 2 * r₀ * (a 2 1).im) : ℝ) : ℂ) • pauli 0 +
      ((2 * ((a 0 1).re * r₁ + (a 2 1).re * r₃ - (a 0 0).re * r₂ - (a 2 2).re * r₂
          + 2 * r₀ * (a 0 2).im) : ℝ) : ℂ) • pauli 1 +
      ((2 * ((a 0 2).re * r₁ + (a 1 2).re * r₂ - (a 0 0).re * r₃ - (a 1 1).re * r₃
          + 2 * r₀ * (a 1 0).im) : ℝ) : ℂ) • pauli 2 := by sorry
end NeutrinoDecoherence
