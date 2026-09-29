-- Prove2me | Theorems.Thm_JechSetTheory_pow_cof_eq_succ_of_isStationary
-- name    : JechSetTheory.pow_cof_eq_succ_of_isStationary
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T02:33:10.46735+00:00
-- url     : https://prove2.me/theorems/16beeb29-da85-4818-9c13-437d8477bfda
-- title:
--   Jech, Lemma 8.14 — $\kappa^{\operatorname{cf}\kappa} = \kappa^{+}$ from a stationary set of good points
-- statement:
--   Write $\operatorname{cf}\kappa$ for the cofinality of a cardinal $\kappa$ and $\kappa^{+}$ for its cardinal successor. A sequence of cardinals $\langle \kappa_\alpha : \alpha < \delta\rangle$ is **normal** if it is strictly increasing and continuous at limit stages.
--
--   **Lemma (Jech 8.14).** Let $\kappa$ be a singular cardinal with $\operatorname{cf}\kappa > \omega$, and assume $\lambda^{\operatorname{cf}\kappa} < \kappa$ for every cardinal $\lambda < \kappa$. Let $\langle \kappa_\alpha : \alpha < \operatorname{cf}\kappa \rangle$ be a normal sequence of cardinals with $\sup_{\alpha} \kappa_\alpha = \kappa$, and suppose that
--
--   $$\bigl\{\, \alpha < \operatorname{cf}\kappa \;:\; \kappa_\alpha^{\operatorname{cf}\kappa_\alpha} = \kappa_\alpha^{+} \,\bigr\}$$
--
--   is a stationary subset of $\operatorname{cf}\kappa$. Then $\kappa^{\operatorname{cf}\kappa} = \kappa^{+}$.
--
--   This is the lemma from which Jech deduces both of Silver's theorems: it says that the value $\kappa^{\operatorname{cf}\kappa}$ is already decided by the behaviour of cardinal exponentiation on a stationary set of stages below $\kappa$. Nothing analogous is available for $\operatorname{cf}\kappa = \omega$, where stationarity is empty of content, which is precisely where Silver's theorem stops.
--
--   **Formalization Note** $\operatorname{cf}\kappa$ is the Mathlib cofinality of the ordinal $\kappa.\mathrm{ord}$, and the normal sequence is a function from the type of ordinals below $\operatorname{cf}\kappa$ to cardinals; "$\lim_\alpha \kappa_\alpha = \kappa$" is the supremum of its range. Stationarity of the set of good stages is stationarity inside the well-ordered type of ordinals below $\operatorname{cf}\kappa$, which is regular and, by hypothesis, uncountable.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 96, Lemma 8.14 (the lemma from which Theorems 8.12 and 8.13 are derived; proof via Lemmas 8.15 and 8.16, pp. 97-98)

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem pow_cof_eq_succ_of_isStationary (k : Cardinal) (hk : k.IsSingular)
    (hcf : ℵ₀ < k.ord.cof) (hsmall : ∀ l < k, l ^ k.ord.cof < k)
    (f : Below k.ord.cof → Cardinal) (hf : IsNormalCardinalSeq f)
    (hlim : ⨆ x, f x = k)
    (hstat : IsStationary {x : Below k.ord.cof | (f x) ^ (f x).ord.cof = Order.succ (f x)}) :
    k ^ k.ord.cof = Order.succ k := by sorry

end JechSetTheory
