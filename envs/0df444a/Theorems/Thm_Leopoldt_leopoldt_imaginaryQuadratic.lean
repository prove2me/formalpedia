-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_imaginaryQuadratic
-- name    : Leopoldt.leopoldt_imaginaryQuadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-09T14:44:58.439046+00:00
-- url     : https://prove2.me/theorems/a26ea79e-13bb-419f-b4cd-5ba6fdc4850e
-- title:
--   Leopoldt's conjecture for imaginary quadratic fields
-- statement:
--   Leopoldt's conjecture holds, at every prime $p$, for every imaginary quadratic field: for $\mathbb{K}$ totally complex with $[\mathbb{K}:\mathbb{Q}] = 2$,
--
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; 0 .$$
--
--   The reason is that such a field has a single infinite place, a complex one, so Dirichlet's unit rank is $r_1 + r_2 - 1 = 0 + 1 - 1 = 0$: the unit group is finite, consisting of roots of unity alone, and there are no $\mathbb{Z}$-independent units that could become $p$-adically dependent. The conjecture is therefore true here for a degenerate reason, and this is the one family of CM fields on which the mission's goal has no content.
--
--   **Formalization note.** "Imaginary quadratic" is spelled as `IsTotallyComplex K` together with $[\mathbb{K}:\mathbb{Q}] = 2$, which for a number field is equivalent to $\mathbb{K} = \mathbb{Q}(\sqrt{d})$ for a squarefree $d < 0$. No hypothesis on $p$ beyond primality is needed, and in particular $p = 2$ is allowed.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.1 (Notations and fundamental facts), p. 3: the defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar), together with Dirichlet's unit theorem as quoted there, "the units E = O(K)^x are a free Z-module of Z-rank r_1 + r_2 - 1". For an imaginary quadratic field r_1 = 0 and r_2 = 1, so the rank is 0 and the defect vanishes; this is the standard observation that Leopoldt's conjecture is trivially true for imaginary quadratic fields.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_imaginaryQuadratic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
