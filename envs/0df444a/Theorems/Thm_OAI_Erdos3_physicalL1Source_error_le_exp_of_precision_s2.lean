-- Prove2me | Theorems.Thm_OAI_Erdos3_physicalL1Source_error_le_exp_of_precision_s2
-- name    : OAI.Erdos3.physicalL1Source_error_le_exp_of_precision_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:30:22.214196+00:00
-- url     : https://prove2.me/theorems/fcca4e46-d9a7-40ab-ae98-5d9fbc6a7cbf
-- title:
--   An explicit physical L1 source error expression is at most exp(-target) once the precision is large enough
-- statement:
--   All named objects below are defined by OpenAI. Let $G$ and $X$ be finite types, $\mathrm{dim}$ a natural number and `selection` an embedding of $\{0,\dots,\mathrm{dim}-1\}$ into $G$. Let $M$, period be natural numbers and $P, D, W, L$, target, precision, $\eta, \varepsilon, \varepsilon_{\mathrm{trunc}}$ real numbers. Assume:
--   - $0 \le P$, $0 < M$, $M \le e^P$, $\mathrm{period} \le e^{P^2}$;
--   - $\mathrm{dim} + 1 \le P$, $|G| \le P$, $|X| \le P$;
--   - $1 \le L$, $0 \le W$, $D \le e^P$, $W \le DL$;
--   - $\mathrm{target} + \texttt{coefficientErrorSpatialLog}\ P + 8 \le \mathrm{precision}$, where `coefficientErrorSpatialLog P` $= P\,(P^3 + \texttt{anisotropicSpatialCapLog}\ P) + P^2(P + 61)$;
--   - $\eta \le e^{-\mathrm{precision}}$, $\varepsilon \le e^{-\mathrm{precision}}$ and $\varepsilon_{\mathrm{trunc}} \le e^{-\mathrm{precision}}$.
--
--   Define
--   $$C_\psi = \Bigl(\mathrm{period}^{\mathrm{dim}+1}\cdot \texttt{anisotropicSpatialDensityCap selection}\ (1/M)\Bigr)^{|X|},$$
--   $$\mathrm{factor} = \Bigl(\frac{30}{\psi(0)}\Bigr)^{(\mathrm{dim}+1)|X|}\Bigl(\Bigl(\frac{1+W}{L}\Bigr)^{\mathrm{dim}}\Bigr)^{|X|},\qquad \mathrm{window} = 9^{|X|(\mathrm{dim}+1)}\Bigl(\Bigl(\frac{1+W}{L}\Bigr)^{\mathrm{dim}}\Bigr)^{|X|},$$
--   where $\psi$ = `smoothProbabilityProfile` is OpenAI's fixed smooth bump probability density on $\mathbb{R}$ and `anisotropicSpatialDensityCap selection κ` is an explicit constant of OpenAI. Then
--   $$C_\psi\Bigl(\mathrm{factor}\cdot\bigl(e^{-\mathrm{precision}} + 2e^{-\mathrm{precision}} + (2\eta + \varepsilon)\bigr) + \mathrm{window}\cdot \varepsilon_{\mathrm{trunc}}\Bigr) \le e^{-\mathrm{target}}.$$
--
--   Lean: `OAI.Erdos3.physicalL1Source_error_le_exp_of_precision_s2`, which states OpenAI's `OAI.Erdos3.physicalL1Source_error_le_exp_of_precision` (in `lean/OAI/Combinatorics/Progressions/Estimates/PhysicalL1SourceAccuracy.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B063` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PhysicalL1SourceAccuracy.lean (declaration OAI.Erdos3.physicalL1Source_error_le_exp_of_precision)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B063

section

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem physicalL1Source_error_le_exp_of_precision_s2 {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target precision : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hprecision : target + coefficientErrorSpatialLog P + 8 ≤ precision)
    {η ε εtrunc : ℝ}
    (hη : η ≤ Real.exp (-precision)) (hε : ε ≤ Real.exp (-precision))
    (ht : εtrunc ≤ Real.exp (-precision)) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (Real.exp (-precision) + 2 * Real.exp (-precision) + (2 * η + ε)) +
      window * εtrunc) ≤ Real.exp (-target) := by
  sorry

end Erdos3

end

end OAI
end
