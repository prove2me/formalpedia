-- Prove2me | Theorems.Thm_Leopoldt_leopoldt_realQuadratic
-- name    : Leopoldt.leopoldt_realQuadratic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:17:28.922917+00:00
-- url     : https://prove2.me/theorems/23958828-1354-4450-ba32-a67851757474
-- title:
--   Leopoldt's conjecture for real quadratic fields
-- statement:
--   Leopoldt's conjecture holds, at every prime $p$, for every real quadratic field: for $\mathbb{K}$ totally real with $[\mathbb{K}:\mathbb{Q}] = 2$,
--
--   $$\mathcal{D}_L(\mathbb{K}) \;=\; 0 .$$
--
--   Such a field has two real places and no complex ones, so Dirichlet's unit rank is $r_1 + r_2 - 1 = 2 + 0 - 1 = 1$: the units are $\pm\varepsilon^{\mathbb{Z}}$ for a fundamental unit $\varepsilon$. Since $\varepsilon$ has infinite order, its $p$-adic closure contains a copy of $\mathbb{Z}_p$, so the $\mathbb{Z}_p$-rank of $\overline{E}$ is $1$ and the defect vanishes. This is the totally real counterpart of the imaginary quadratic case.
--
--   **Formalization note.** "Real quadratic" is spelled as `IsTotallyReal K` together with $[\mathbb{K}:\mathbb{Q}] = 2$, which for a number field is equivalent to $\mathbb{K} = \mathbb{Q}(\sqrt{d})$ for a squarefree $d > 1$. No hypothesis on $p$ beyond primality is needed.
-- source:
--   Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016), Section 1.1 (Notations and fundamental facts), p. 3: the Leopoldt defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar) and Dirichlet's unit theorem as quoted there ("the units E = O(K)^x are a free Z-module of Z-rank r_1 + r_2 - 1"). For a real quadratic field r_1 = 2 and r_2 = 0, so the unit rank is 1 and, since the defect is at most rank - 1, the defect vanishes; this is the standard observation that Leopoldt's conjecture holds for real quadratic fields.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldt_realQuadratic (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]
    (hK : Module.finrank ℚ K = 2) :
    LeopoldtConjecture p K := by sorry
end Leopoldt
