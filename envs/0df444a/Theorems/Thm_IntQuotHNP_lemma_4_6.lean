-- Prove2me | Theorems.Thm_IntQuotHNP_lemma_4_6
-- name    : IntQuotHNP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:50.996195+00:00
-- url     : https://prove2.me/theorems/47b89ac8-bed9-4d7d-93bb-89bdd6f0e935
-- title:
--   Lemma 4.6 — bounded rational values: $\Pr[|f_h(z)|_p\le R\ \forall h]\ll_{j,D}(R/p)^j+p^{-1/2}$
-- statement:
--   Fix integers $j,D\ge1$. There are $C$ and $p_0$ with the following property. Let $p\ge p_0$ be prime and let $f_1,\dots,f_j$ be rational functions over $\mathbb F_p$ whose reduced numerators and denominators have degree at most $D$, such that every linear combination with coefficients not all zero is nonconstant and has only simple poles, including at infinity. Let $\Omega\subseteq\mathbb Z_p$ consist of points where all $f_h$ are defined, with $|\mathbb Z_p\setminus\Omega|\le D$, and let $1\le R\le(p-1)/4$ be an integer. Then for $z$ uniform on $\Omega$,
--   $$
--   \Pr\bigl[\,|f_h(z)|_p\le R\ \text{ for every }h\,\bigr]\le C\Bigl(\bigl(\tfrac Rp\bigr)^j+p^{-1/2}\Bigr).
--   $$
--   This bounds how often rational functions of one sampled inverse are simultaneously small, and it supplies the $E_j(u)$ factors of Lemma 4.4.
--
--   Differences from the source:
--   - encoding: ≪_{j,D} and sufficiently large p → ∃ C, p₀ chosen after j, D and before p and the functions; reason: this is the meaning of the notation
--   - encoding: only simple poles, including at infinity; nonconstant → RatFunc.denom separable, deg num ≤ deg denom + 1, and not equal to any RatFunc.C c; reason: these conditions are equivalent to the source's, stated on the reduced fraction
--   - encoding: z uniform on Ω; |ℤ_p \ Ω| ≤ D; R ≤ (p − 1)/4 → the ratio of cardinalities over a Finset of ZMod p; p − |Ω| ≤ D; 4R ≤ p − 1; reason: the same quantities on ZMod p and natural numbers
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 4.6, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_IntQuotHNP_Sampling
import Definitions.Def_IntQuotHNP_RationalValues

namespace IntQuotHNP

/-- **Lemma 4.6 (bounded rational values).**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), Lemma 4.6, p.25 (PDF p.26): "Fix integers j, D ≥ 1. Let f₁, . . . , f_j be rational
functions modulo p whose reduced numerators and denominators have degree at most D. Suppose every
linear combination with coefficients not all zero modulo p is nonconstant and has only simple poles,
including at infinity. Let Ω ⊆ ℤ_p consist of points where all f_h are defined, with
|ℤ_p \ Ω| ≤ D. For sufficiently large p, an integer 1 ≤ R ≤ (p − 1)/4, and z uniform on Ω,
Pr[|f_h(z)|_p ≤ R for every h ∈ [j]] ≪_{j,D} (R/p)^j + p^{−1/2}."

For all `j, D ≥ 1` there are `C` and `p₀` such that for every prime `p ≥ p₀`, all rational
functions `f₁, …, f_j` over `𝔽_p` whose reduced numerators and denominators have degree `≤ D` and
every nonzero linear combination of which is nonconstant with only simple poles (also at infinity),
every set `Ω` of points where all `f_h` are defined with `|ℤ_p \ Ω| ≤ D`, and every integer
`1 ≤ R ≤ (p − 1)/4`:
$$\Pr_{z \in \Omega}[\,|f_h(z)|_p \le R\ \forall h\,] \le C\,((R/p)^j + p^{-1/2}).$$

**Formalization Note.** `C` and `p₀` depend only on `j` and `D`. `Ω` is a finite set of residues
and `|ℤ_p \ Ω|` is `p − |Ω|`. A linear combination with coefficients `c ∈ 𝔽_p^j \ {0}` is
`∑ C(c_h)·f_h`. -/
theorem lemma_4_6 (j D : ℕ) (hj : 1 ≤ j) (hD : 1 ≤ D) :
    ∃ (C : ℝ) (p₀ : ℕ), ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ∀ f : Fin j → RatFunc (ZMod p),
        (∀ h, (f h).num.natDegree ≤ D ∧ (f h).denom.natDegree ≤ D) →
        (∀ c : Fin j → ZMod p, c ≠ 0 →
          IsNonconstant (∑ h, RatFunc.C (c h) * f h) ∧
            HasOnlySimplePoles (∑ h, RatFunc.C (c h) * f h)) →
        ∀ Ω : Finset (ZMod p), (∀ z ∈ Ω, ∀ h, (f h).denom.eval z ≠ 0) → p - Ω.card ≤ D →
        ∀ R : ℕ, 1 ≤ R → 4 * R ≤ p - 1 →
          prob Ω (fun z => ∀ h, absP p (ratEval (f h) z) ≤ R) ≤
            C * (((R : ℝ) / p) ^ j + (p : ℝ) ^ (-(1 / 2 : ℝ))) := by sorry

end IntQuotHNP
