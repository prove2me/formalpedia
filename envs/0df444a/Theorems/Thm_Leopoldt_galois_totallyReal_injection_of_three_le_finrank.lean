-- Prove2me | Theorems.Thm_Leopoldt_galois_totallyReal_injection_of_three_le_finrank
-- name    : Leopoldt.galois_totallyReal_injection_of_three_le_finrank
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T02:17:40.104164+00:00
-- url     : https://prove2.me/theorems/b96cd1bf-d41d-4fbb-9fa8-b93ee548dca8
-- title:
--   $p$-adic regulator injection for Galois totally real fields of degree $\ge 3$
-- statement:
--   Let $p$ be an odd prime and let $\mathbb{L}$ be a totally real number field, Galois over $\mathbb{Q}$, of degree $[\mathbb{L}:\mathbb{Q}] \ge 3$ (equivalently, of unit rank $r = [\mathbb{L}:\mathbb{Q}] - 1 \ge 2$). Then there is a continuous injective group homomorphism
--
--   $$f \colon \mathbb{Z}_p^{\,r} \hookrightarrow U(\mathbb{L}) = \prod_{v \mid p} \mathcal{O}_{\mathbb{L}_v}^\times$$
--
--   into the semilocal units at $p$, all of whose values lie in the $p$-adic closure $\overline{E}$ of the global units $E$. By the characterization `Leopoldt.leopoldtConjecture_iff_exists_continuous_injection`, this is exactly Leopoldt's conjecture $\mathcal{D}_L(\mathbb{L}) = 0$ for such $\mathbb{L}$.
--
--   This is the lemma `Leopoldt.galois_totallyReal_injection` restricted to degree at least $3$; the excluded degrees $1$ and $2$ ($\mathbb{Q}$ and real quadratic fields) have unit rank at most $1$, where the conjecture holds for elementary reasons. The remaining case is the genuine research-level content of Leopoldt's conjecture for Galois totally real fields.
-- source:
--   Restriction to degree >= 3 of Leopoldt.galois_totallyReal_injection (the p-adic regulator formulation of Leopoldt's conjecture, equivalent to it via Leopoldt.leopoldtConjecture_iff_exists_continuous_injection). The Galois totally real case is the research-scale case isolated in Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544, Section 1.1, where D_L(K) = Z-rk(E) - Z_p-rk(Ebar) and the unit rank is r_1 + r_2 - 1 (= [L:Q] - 1 for L totally real).

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem galois_totallyReal_injection_of_three_le_finrank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (L : Type*) [Field L] [NumberField L] [IsTotallyReal L] [IsGalois ℚ L]
    (hL : 3 ≤ Module.finrank ℚ L) :
    ∃ f : Multiplicative (Fin (Units.rank L) → ℤ_[p]) →* SemilocalUnits p L,
      Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ unitClosure p L := by sorry
end Leopoldt
