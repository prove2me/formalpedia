-- Prove2me | Theorems.Thm_ModFormPIR_corollary_10_36
-- name    : ModFormPIR.corollary_10_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:59.580264+00:00
-- url     : https://prove2.me/theorems/e1c2cdea-af4c-49d5-b47c-ea7061f00e9d
-- title:
--   Corollary 10.36, p.49 — the valence formula for $\Gamma(q)$
-- statement:
--   Let $q$ be an odd prime and let $f:\mathbb H\to\mathbb C$ be a modular form of weight $k$ for $\Gamma(q)$ with a one-dimensional representation $\chi$, $\chi^j=1$ for some positive integer $j$, with $f$ not identically zero. Then
--   $$\sum_{\text{cusps }c}\frac{\mathrm{ord}_c(f)}2+\sum_{\tau\in\mathbb H/\Gamma(q)}\frac{\mathrm{ord}_\tau(f)}{2\,|\{g\in\Gamma(q):g*\tau=\tau\}|}=\frac k{24}\cdot\frac{q^3-q}2,$$
--   where the first sum ranges over the $\Gamma(q)$-classes of cusps, with widths and orders with respect to $\Gamma(q)$, and the second over the $\Gamma(q)$-classes of zeros of $f$ in $\mathbb H$.
--
--   This is the root count that ends the proof, playing the part of the degree bound for a univariate polynomial.
--
--   **Formalization Note** Sums are `finsum` over the quotients, using a chosen representative per class.
--
--   Differences from the source:
--   - encoding: classes of cusps of ℚ ∪ {∞} → first columns of g ∈ SL₂(ℤ) modulo q, up to sign, with order computed at a representative; reason: Proposition 12.23; the first clauses state that orders are finite and class-invariant (Lemma 10.28)
--   - encoding: ord_c from Fourier expansion (24)–(25) → sup of r with f_g(τ) e^{−2πirτ/q} bounded as Im τ → ∞; reason: equivalent for a scalar with a finite-order character; checked in the sanity file on Δ
--   - encoding: second sum over zeros, finite by Theorem 10.35 → `finsum` over all orbits, terms at non-zeros being 0, with a clause that the zero classes are finite; reason: the same sum
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Corollary 10.36, p.49 (PDF p.53), with Theorem 10.35, pp.48–49

import Mathlib
import Definitions.Def_ModFormPIR_CharForms

open scoped MatrixGroups UpperHalfPlane

set_option autoImplicit false

namespace ModFormPIR

/-- **Corollary 10.36** (Valence formula for `Γ(q)`), p.49, (29). Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For `f ≢ 0` a modular form of weight `k` for `Γ(q)` with a one-dimensional representation `χ`, `χ^j = 1`:
`∑_{cusps c} ord_c(f)/2 + ∑_{τ ∈ ℍ/Γ(q)} ord_τ(f)/(2|{g ∈ Γ(q) : g∗τ = τ}|) = (k/24)·(q³-q)/2`.

**Formalization Note.** The first sum is over `CuspClass q`, the second over `PointClass q`, with a chosen representative for each; the clauses before the identity state that the cusp orders are finite and depend only on the
class (Lemma 10.28), and that `f` has finitely many classes of zeros (Theorem 10.35). Terms at non-zeros vanish, so the second sum is over classes of zeros. -/
theorem corollary_10_36 (q : ℕ) [Fact q.Prime] (hodd : Odd q) (k : ℕ) (f : ℍ → ℂ)
    (hf : IsModularFormChar q k f) (hne : ∃ τ, f τ ≠ 0) :
    (∀ g : SL(2, ℤ), cuspOrd q k f g ≠ ⊤ ∧ cuspOrd q k f g ≠ ⊥) ∧
    (∀ g h : SL(2, ℤ), (cuspSetoid q).r g h → cuspOrd q k f g = cuspOrd q k f h) ∧
    {x : PointClass q | f (Quotient.out x) = 0}.Finite ∧
    (∑ᶠ c : CuspClass q, (cuspOrd q k f (Quotient.out c)).toReal / 2) +
      (∑ᶠ x : PointClass q, (pointOrd f (Quotient.out x) : ℝ) /
        (2 * (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma q) (Quotient.out x)) : ℝ))) =
      ((k : ℝ) / 24) * (((q : ℝ) ^ 3 - q) / 2) := by sorry

end ModFormPIR
