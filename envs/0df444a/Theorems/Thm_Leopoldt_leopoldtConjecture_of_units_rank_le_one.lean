-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_of_units_rank_le_one
-- name    : Leopoldt.leopoldtConjecture_of_units_rank_le_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:17:30.793839+00:00
-- url     : https://prove2.me/theorems/a14cc072-b6ab-4a19-8c26-b44da8c39bf4
-- title:
--   Leopoldt's conjecture for number fields of unit rank at most $1$
-- statement:
--   Let $p$ be a prime and let $\mathbb{K}$ be a number field whose Dirichlet unit rank $r = r_1 + r_2 - 1$ is at most $1$. Then Leopoldt's conjecture holds for $\mathbb{K}$ at $p$:
--
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; 0 .$$
--
--   Here $\mathcal{D}_L(\mathbb{K}) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\overline{E})$ is the Leopoldt defect: the unit rank minus the $\mathbb{Z}_p$-rank of the $p$-adic closure $\overline{E}$ of the global units $E$ inside the semilocal units at $p$. The reason is that any unit of infinite order stays of infinite order $p$-adically, so the defect is always at most $r - 1$; when $r \le 1$ this forces the defect to vanish. The fields covered are exactly $\mathbb{Q}$, the imaginary quadratic fields ($r = 0$), and the fields with $r = 1$: real quadratic fields, cubic fields with one real place, and totally imaginary quartic fields.
--
--   **Formalization note.** `Units.rank K` is Mathlib's Dirichlet unit rank and `LeopoldtConjecture p K` is the platform predicate `defect p K = 0` from `Def_LeopoldtDefect`. No restriction on $p$ beyond primality is needed.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.1 (Notations and fundamental facts), p. 3: the Leopoldt defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar) and Dirichlet's unit theorem as quoted there ("the units E = O(K)^x are a free Z-module of Z-rank r_1 + r_2 - 1"). Since a unit of infinite order generates a copy of Z_p in Ebar, D_L(K) <= r - 1 (platform theorem Leopoldt.defect_le_units_rank_sub_one), hence D_L(K) = 0 when r <= 1; this is the standard observation that Leopoldt's conjecture is trivial in unit rank at most one.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldtConjecture_of_units_rank_le_one (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (h : Units.rank K ≤ 1) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
