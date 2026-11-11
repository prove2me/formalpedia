-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_4_13
-- name    : LeakageRefresh.Continual.lemma_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:11:50.251139+00:00
-- url     : https://prove2.me/theorems/d643e74a-3c9a-4d86-96a2-f7a4ffb61522
-- title:
--   Lemma 4.13 — local approximation for a refresh: one table $G_{i,h,z}$ with $\|G\|_*\le4$, energies $\le2/\beta$ pointwise and $\le4$ on average, error $\le\varepsilon=Cq^{-1/9}$
-- statement:
--   There is an absolute constant $C>0$ such that, with $q=2^n-1$, $\beta=q^{-1/3}$ and $\varepsilon=Cq^{-1/9}$, the following holds for every $n\ge2$, every $T,\lambda$ and every deterministic strategy. For every round $i$, formal incoming history $h\in\mathcal Z^{i-1}$ and answer $z$ there is a single table $G=G_{i,h,z}$ on $U_L^2\times U_R^2$ with a product representation whose energies $\Phi,\Psi$ satisfy
--   $$\|G\|_*\le4,\quad\Phi\le\frac2\beta,\quad\Psi\le\frac2\beta,\quad\mathbb E[\Phi]\le4,\quad\mathbb E[\Psi]\le4, \tag{4.58–4.62}$$
--   $$\|\mathrm{prob}_{i,h,z}-G\|_{2,\mu_s\otimes\mu_s}\le\varepsilon\ \ (s\in\{0,1\}),\qquad\|G\|_{2,\mu_s\otimes\mu_{s'}}\le6\ \ ((s,s')\in\{0,1\}^2). \tag{4.63–4.64}$$
--   The same table and representation serve both secrets and all label pairs, and all bounds are uniform over formal histories, including unreachable ones.
--
--   Differences from the source:
--   - encoding: rounds $i\in\{1,\dots,T\}$ with incoming history $h\in\mathcal Z^{i-1}$ → `i : Fin T` is round $i+1$, with incoming history `Fin i → Answer lam`; reason: 0-based indexing of the same rounds and histories
--   - encoding: the seven conclusions (4.58)–(4.64) for one table with a chosen product representation → `IsLocalApprox (σ i h) z β ε G`, which bundles exactly these conclusions with one `ProdRep G`; reason: a named predicate for the lemma's conclusion, reused by Eq. (4.69)
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 41, Lemma 4.13

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_LeakageModel
import Definitions.Def_LeakageRefresh_Continual_Tables
import Definitions.Def_LeakageRefresh_Continual_OneRound

namespace LeakageRefresh.Continual

/-- **Lemma 4.13 (Local approximation for a refresh).** There is an absolute constant `C > 0`
such that, with `q = 2ⁿ − 1`, `β = q^{−1/3}` and `ε = C q^{−1/9}`, for every `n ≥ 2`, every
strategy, every round `i`, formal incoming history `h` and answer `z`, there is a single table
`G_{i,h,z}` on `U_L² × U_R²` with a product representation satisfying (4.58)–(4.64)
(`IsLocalApprox`) for both secrets and all label pairs at once. -/
theorem lemma_4_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n T lam : ℕ, 2 ≤ n →
      ∀ (σ : Strategy n T lam) (i : Fin T) (h : Fin i → Answer lam) (z : Answer lam),
        ∃ G : Table4 n,
          IsLocalApprox (σ i h) z (((2 : ℝ) ^ n - 1) ^ (-(1 / 3 : ℝ)))
            (C * ((2 : ℝ) ^ n - 1) ^ (-(1 / 9 : ℝ))) G := by sorry

end LeakageRefresh.Continual
