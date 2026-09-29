-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
-- name    : ModularCurve.exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c77ca4f7-cc9c-58c2-9f48-50266e28385c
-- title:
--   Mod p reduction on a Gauss valuation subring of ℚ((q))
-- statement:
--   Let $p$ be a prime, let $F_0$ be an intermediate field of the extension $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (Laurent series with rational coefficients), and let $W$ be a valuation subring of $F_0$. Write $\iota$ for the coefficientwise map `coeffMap (Int.castRingHom ℚ)` from $\mathbb{Z}((q))$ to $\mathbb{Q}((q))$ and $y \mapsto \bar y$ for the coefficientwise map `coeffMap (Int.castRingHom (ZMod p))` from $\mathbb{Z}((q))$ to $(\mathbb{Z}/p)((q))$, both obtained by applying a ring homomorphism to each coefficient of a Laurent series. Assume that $W$ is the Gauss valuation ring in the following explicit sense: an element $f \in F_0$ lies in $W$ if and only if there are $x, y \in \mathbb{Z}((q))$ with $\bar y \neq 0$ and $f \cdot \iota(y) = \iota(x)$ in $\mathbb{Q}((q))$. Then there exists a ring homomorphism $\mathrm{red} : W \to (\mathbb{Z}/p)((q))$ such that, first, for $f \in W$ one has $\mathrm{red}(f) = 0$ if and only if $f$, viewed in $F_0$, belongs to `W.nonunits`, the elements of $F_0$ of $W$-valuation $< 1$ (for elements of $W$, exactly the non-units of $W$, i.e. its maximal ideal); and second, for every $f \in W$ and all $x, y \in \mathbb{Z}((q))$ with $\bar y \neq 0$ and $f \cdot \iota(y) = \iota(x)$, one has $\mathrm{red}(f) \cdot \bar y = \bar x$. Thus $\mathrm{red}$ is coefficientwise reduction of $q$-expansions modulo $p$, computed as $\bar x/\bar y$ from any such representation, and it induces an embedding of the residue field of $W$ into $\mathbb{F}_p((q))$.
--
--   This is Gauss's lemma for the $p$-adic Gauss valuation on a field of rational $q$-expansions, in the form of a $q$-expansion principle: reduction modulo $p$ of $q$-expansions is a well-defined ring homomorphism onto a subring of $\mathbb{F}_p((q))$ whose kernel is the maximal ideal of the valuation ring. It is used in the construction of mod $p$ reductions of modular function fields, being cited in the work on the Igusa scheme and on the Deligne–Rapoport model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_ringHom_laurentSeries_zmod_of_gaussValuationSubring
    (p : ℕ) [Fact p.Prime] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (W : ValuationSubring ↥F₀)
    (hW : ∀ f : ↥F₀, f ∈ W ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) :
    ∃ red : ↥W →+* LaurentSeries (ZMod p),
      (∀ f : ↥W, red f = 0 ↔ (f : ↥F₀) ∈ W.nonunits) ∧
      ∀ (f : ↥W) (x y : LaurentSeries ℤ), coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 →
        ((f : ↥F₀) : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y =
          coeffMap (Int.castRingHom ℚ) x →
        red f * coeffMap (Int.castRingHom (ZMod p)) y = coeffMap (Int.castRingHom (ZMod p)) x := by sorry
