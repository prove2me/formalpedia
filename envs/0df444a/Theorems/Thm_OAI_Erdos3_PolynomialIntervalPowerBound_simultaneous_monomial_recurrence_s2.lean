-- Prove2me | Theorems.Thm_OAI_Erdos3_PolynomialIntervalPowerBound_simultaneous_monomial_recurrence_s2
-- name    : OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:19:32.10799+00:00
-- url     : https://prove2.me/theorems/a37ec4c6-65a7-4e3b-bd5e-ef3a9db0af4b
-- title:
--   A Weyl-type inverse bound in degree j+1 gives simultaneous recurrence of the monomial q^(j+1) modulo 1
-- statement:
--   Let $j, C, e$ be natural numbers and assume `PolynomialIntervalPowerBound (j+1) C e`, a proposition defined by OpenAI. It says: for every real polynomial $P$ with $\deg P \le j+1$, all integers $u, v$ with $v - u > 0$, and every real $\delta$ with $0 < \delta \le 1$, if $C \le \delta^{e}(v-u)$ and
--   $$\delta\,(v-u) \le \Bigl|\sum_{n=u}^{v-1} \exp(2\pi i P(n))\Bigr|,$$
--   then there are a natural number $q$ with $0 < q \le C/\delta^{e}$ and an integer $p$ with $|q\,a_{j+1} - p| \le C/(\delta^{e}(v-u)^{j+1})$, where $a_{j+1}$ is the coefficient of $X^{j+1}$ in $P$.
--
--   Let $\iota$ be a finite type with $|\iota|$ elements, let $\alpha : \iota \to \mathbb{R}$, let $N$ be a natural number, and let $R$ be a real number with $0 < R \le 1$. Suppose
--   $$\left(\frac{\texttt{schmidtRecurrenceBase}\ C\ e \cdot (|\iota| + 1)}{R}\right)^{\texttt{schmidtRecurrenceExponent}\ e\ \cdot\ (|\iota|+1)^2} \le N,$$
--   where `schmidtRecurrenceExponent e` $= 15(e+1) + 23$ and `schmidtRecurrenceBase C e` $= 2 + 121\exp(10) + \texttt{schmidtDegreeConstant}\ C\ e + \texttt{schmidtRecurrenceExponent}\ e$, with `schmidtDegreeConstant C e` $= (10 + 8\exp(4\pi+1))(1 + 2\exp(\pi)\, C\, 8^{e})$ (all defined by OpenAI; here $\exp$ is the real exponential, while $e$ is the natural number above). Then there is a natural number $q$ with $0 < q \le N$ and integers $m_i$ ($i \in \iota$) such that $|q^{j+1}\alpha_i - m_i| < R$ for every $i \in \iota$.
--
--   Lean: `OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2`, which states OpenAI's `OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence` (in `lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B037`, `OAIE3v2B137` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Polynomial/PolynomialCoordinatePartition.lean (declaration OAI.Erdos3.PolynomialIntervalPowerBound.simultaneous_monomial_recurrence)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B037
import Definitions.Def_OAIE3v2B137

section

namespace OAI

section

namespace Erdos3

theorem PolynomialIntervalPowerBound.simultaneous_monomial_recurrence_s2
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (α : ι → ℝ) (N : ℕ) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hN : (schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) / R) ^
      (schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ≤ N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ ∃ m : ι → ℤ, ∀ i, |(q : ℝ) ^ (j + 1) * α i - m i| < R := by
  sorry

end Erdos3

end

end OAI
end
