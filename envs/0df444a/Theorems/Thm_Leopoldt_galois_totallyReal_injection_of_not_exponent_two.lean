-- Prove2me | Theorems.Thm_Leopoldt_galois_totallyReal_injection_of_not_exponent_two
-- name    : Leopoldt.galois_totallyReal_injection_of_not_exponent_two
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T20:23:13.667392+00:00
-- url     : https://prove2.me/theorems/2f6264a6-6b6a-4cc6-9567-899387e26d6d
-- title:
--   Leopoldt injection for Galois totally real fields whose Galois group is not of exponent 2
-- statement:
--   Let $p$ be an odd prime and let $\mathbb{L}$ be a totally real number field, Galois over $\mathbb{Q}$, of degree $[\mathbb{L}:\mathbb{Q}] \ge 3$, whose Galois group $G = \mathrm{Gal}(\mathbb{L}/\mathbb{Q})$ is **not** of exponent $2$: some $\sigma \in G$ has $\sigma^2 \neq 1$. Then, with $r = [\mathbb{L}:\mathbb{Q}] - 1$ the unit rank, there is a continuous injective group homomorphism
--
--   $$f \colon \mathbb{Z}_p^{\,r} \hookrightarrow U(\mathbb{L}) = \prod_{v \mid p} \mathcal{O}_{\mathbb{L}_v}^\times$$
--
--   into the semilocal units at $p$, all of whose values lie in the $p$-adic closure $\overline{E}$ of the global units $E$. By `Leopoldt.leopoldtConjecture_iff_exists_continuous_injection` this is Leopoldt's conjecture $\mathcal{D}_L(\mathbb{L}) = 0$ for such $\mathbb{L}$.
--
--   This is `Leopoldt.galois_totallyReal_injection_of_three_le_finrank` with the multiquadratic fields removed. When every $\sigma \in G$ satisfies $\sigma^2 = 1$, $\mathbb{L} = \mathbb{Q}(\sqrt{a_1},\dots,\sqrt{a_k})$ is a totally real multiquadratic field, and there the conjecture is proved (`Leopoldt.leopoldt_totallyReal_multiquadratic`) by the eigen-decomposition of the units under the characters $G \to \{\pm 1\}$. The remaining fields, for instance cyclic cubic fields or real subfields of $\mathbb{Q}(\zeta_{p^n})$ of degree $> 2$, are exactly those in which some Galois eigenspace of $E \otimes \overline{\mathbb{Q}}_p$ is attached to a character of order greater than $2$. This is where the genuine difficulty of Leopoldt's conjecture for Galois totally real fields lies; for abelian $\mathbb{L}$ it is Brumer's theorem, which relies on Baker's theory of linear forms in $p$-adic logarithms.
-- source:
--   Restriction of Leopoldt.galois_totallyReal_injection_of_three_le_finrank to Galois groups not of exponent 2 (the exponent-2 case being Leopoldt.leopoldt_totallyReal_multiquadratic). Leopoldt's conjecture for Galois totally real fields: Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1; abelian case: A. Brumer, On the units of algebraic number fields, Mathematika 14 (1967), 121-124; L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Section 5.5, Theorem 5.29.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem galois_totallyReal_injection_of_not_exponent_two (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L]
    (hL : 3 ≤ Module.finrank ℚ L) (hG : ∃ σ : L ≃ₐ[ℚ] L, σ * σ ≠ 1) :
    ∃ f : Multiplicative (Fin (Units.rank L) → ℤ_[p]) →* SemilocalUnits p L,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ unitClosure p L := by sorry
end Leopoldt
