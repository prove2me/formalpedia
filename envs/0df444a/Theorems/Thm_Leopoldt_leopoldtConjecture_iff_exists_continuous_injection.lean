-- Prove2me | Theorems.Thm_Leopoldt_leopoldtConjecture_iff_exists_continuous_injection
-- name    : Leopoldt.leopoldtConjecture_iff_exists_continuous_injection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:21.880115+00:00
-- url     : https://prove2.me/theorems/dfe9dcf3-8e83-4386-a695-5f96f0499f32
-- title:
--   Leopoldt's conjecture as a single continuous injection $\mathbb{Z}_p^{\,r} \hookrightarrow \bar{E}$
-- statement:
--   In the formalisation, the $\mathbb{Z}_p$-rank of a subgroup $H$ of the semilocal units is defined as a supremum,
--
--   $$\mathbb{Z}_p\text{-rk}(H) \;=\; \sup\,\{\, n \le [\mathbb{K}:\mathbb{Q}] \;:\; \text{there is a continuous injective homomorphism } \mathbb{Z}_p^{\,n} \to H \,\},$$
--
--   and Leopoldt's conjecture is the vanishing of $\mathcal{D}_L(\mathbb{K}) = \mathbb{Z}\text{-rk}(E) - \mathbb{Z}_p\text{-rk}(\bar{E})$. This theorem removes the supremum: Leopoldt's conjecture for $\mathbb{K}$ at $p$ holds **if and only if** there is a single continuous injective homomorphism
--
--   $$\mathbb{Z}_p^{\,r} \;\longrightarrow\; U \;=\; \prod_{\wp \mid p} \mathcal{O}_\wp^{\times}, \qquad r \;=\; \mathbb{Z}\text{-rk}(E) \;=\; r_1 + r_2 - 1,$$
--
--   whose image lies in the $p$-adic closure $\bar{E}$ of the global units.
--
--   The content is bookkeeping, but it is the bookkeeping every attempt on the conjecture needs. In one direction a witness exhibits the rank directly. In the other, the supremum is attained - the set of admissible $n$ is a set of naturals containing $0$ and bounded by $[\mathbb{K}:\mathbb{Q}]$ - and it is downward closed, because an injection of $\mathbb{Z}_p^{\,n}$ restricts along the zero-padding $\mathbb{Z}_p^{\,m} \hookrightarrow \mathbb{Z}_p^{\,n}$ for $m \le n$; the cut-off $r \le [\mathbb{K}:\mathbb{Q}]$ needed to apply this is Dirichlet's $r_1 + r_2 - 1 \le r_1 + 2r_2$.
--
--   **Formalization note.** The source group of the homomorphism is written `Multiplicative (Fin r -> Z_[p])`, the additive group $\mathbb{Z}_p^{\,r}$ viewed multiplicatively, matching the definition of the rank; `Continuous` refers to the product topology on it and to the topology of `SemilocalUnits p K`. Continuity is what makes the rank the intended one: as abstract groups $\mathbb{Z}_p^{\,n}$ embeds into $\mathbb{Z}_p$ for every $n$.
-- source:
--   This is an unfolding of the definitions of the mission's definition file Definitions.Def_LeopoldtDefect, which formalises Section 1.1 (Notations and fundamental facts), pp. 2-3, of Preda Mihailescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, https://arxiv.org/abs/1105.4544 (v4, 17 Feb 2016): the semilocal units U = prod_{wp | p} O_wp^x, the diagonal embedding iota : E -> U, the p-adic closure Ebar = intersection_{n>0} iota(E).U^{p^n}, and the defect D_L(K) = Z-rk(E) - Z_p-rk(Ebar). No mathematical input beyond those definitions and Dirichlet's unit theorem (for the bound r_1 + r_2 - 1 <= [K:Q]) is used.

import Definitions.Def_LeopoldtDefect

open NumberField

namespace Leopoldt
theorem leopoldtConjecture_iff_exists_continuous_injection (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] :
    LeopoldtConjecture p K ↔
      ∃ f : Multiplicative (Fin (Units.rank K) → ℤ_[p]) →* SemilocalUnits p K,
        Function.Injective f ∧ Continuous f ∧ ∀ x, f x ∈ unitClosure p K := by sorry
end Leopoldt
