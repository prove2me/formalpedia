-- Prove2me | Theorems.Thm_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow
-- name    : ModularCurve.coeff_inv_mul_thetaL_mul_char_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/cf69f901-14f2-57b7-8485-93b72dd56faf
-- title:
--   Cartier fixedness of the logarithmic q-derivative
-- statement:
--   Let $k$ be a field, $p$ a prime and suppose $k$ has characteristic $p$. Let $f$ be a Laurent series over $k$ (an element of `LaurentSeries k`, the Hahn series field over $\mathbb{Z}$ with coefficients in $k$), assumed nonzero, and let $n$ be an integer. Here `thetaL k` denotes the $k$-linear operator $f \mapsto \mathfrak{q}\,\mathrm{d}f/\mathrm{d}\mathfrak{q}$, realised as multiplication of the formal derivative `LaurentSeries.derivative k f` by the Hahn series `single (1 : ℤ) (1 : k)`, i.e. by $\mathfrak{q}$; on coefficients it sends $\sum_m c_m \mathfrak{q}^m$ to $\sum_m m\,c_m \mathfrak{q}^m$. Since $f \neq 0$ it is invertible in the field of Laurent series, so the logarithmic $q$-derivative $f^{-1}\,\theta f$ is defined. The assertion is that its coefficients $a_m = (f^{-1} \cdot \theta f).\mathrm{coeff}(m)$ satisfy $$a_{np} = (a_n)^p$$ for the given $n$, and hence, $n$ being arbitrary, for every integer $n$.
--
--   In the language of differentials this is the statement that the logarithmic differential $\mathrm{d}f/f$ is fixed by the Cartier operator $C\big(\sum_n a_n \mathfrak{q}^n\,\mathrm{d}\mathfrak{q}/\mathfrak{q}\big) = \sum_n a_{np}^{1/p}\,\mathfrak{q}^n\,\mathrm{d}\mathfrak{q}/\mathfrak{q}$ in characteristic $p$, expressed purely in terms of $q$-expansion coefficients. Together with the vanishing of the coefficients in negative degrees and the value $\operatorname{ord}(f)$ in degree $0$, it is used to pin down the $q$-expansions of logarithmic differentials attached to $p$-torsion divisor classes in characteristic $p$, in the results on spans of logarithmic differentials and on Eisenstein fibres of the Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_inv_mul_thetaL_mul_char_eq_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_inv_mul_thetaL_mul_char_eq_pow
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : LaurentSeries k) (hf : f ≠ 0) (n : ℤ) :
    (f⁻¹ * thetaL k f).coeff (n * p) = ((f⁻¹ * thetaL k f).coeff n) ^ p := by sorry
