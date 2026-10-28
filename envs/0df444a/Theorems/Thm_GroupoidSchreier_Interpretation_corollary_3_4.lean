-- Prove2me | Theorems.Thm_GroupoidSchreier_Interpretation_corollary_3_4
-- name    : GroupoidSchreier.Interpretation.corollary_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:32.097029+00:00
-- url     : https://prove2.me/theorems/3e9ac4b9-790d-4bf8-8db7-57cd72593119
-- title:
--   Corollary 3.4, p. 15 — H² of a groupoid with coefficients in AUT(K) is in bijection with the connected components of Ext(G, K)
-- statement:
--   **Corollary 3.4 (Interpretation of groupoid cohomology).** For any groupoid $\mathcal G$ and any family of groups $\mathcal K = \{K_A\}$ indexed by the objects of $\mathcal G$, there is a bijection
--
--   $$H^2_{|\mathrm{AUT}(\mathcal K)|}(\mathcal G,\mathcal K)\ \cong\ \mathrm{Ext}[\mathcal G,\mathcal K]$$
--
--   between the cohomology classes of weak actions (2-cocycles) of $\mathcal G$ with coefficients in the 2-groupoid $\mathrm{AUT}(\mathcal K)$ and the connected components of the category $\mathrm{Ext}(\mathcal G,\mathcal K)$ of extensions of $\mathcal G$ by $\mathcal K$. It is the bijection induced by Theorem 3.2: whenever a weak action $F$ is a fiber weak action of an extension $\mathcal E$ (Example 2.15), the class $[F]$ is sent to $[\mathcal E]$.
--
--   This is the groupoid version of Schreier's classification of group extensions with non abelian kernel.
--
--   **Formalization Note** The page's prose says "a bijection between the 2-cocycles … and the connected components"; the displayed formula has $H^2$, the set of connected components of 2-cocycles, on the left, and the statement follows the formula. The compatibility clause pins the bijection to the paper's (a bare existence of some bijection would only compare cardinalities). For some $(\mathcal G,\mathcal K)$ — an arrow $A\to B$ with $K_A\not\cong K_B$ — there is no weak action and no extension at all, and both sides are empty, as in the paper.
-- source:
--   Blanco, Bullejos & Faro, Categorical non abelian cohomology, and the Schreier theory of groupoids, arXiv:math/0410202v1, p. 15, Corollary 3.4

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
theorem corollary_3_4 (G : Type u) [Groupoid.{u} G] (K : G → Type u) [∀ A, Group (K A)] :
    ∃ e : H2 G K ≃ ExtClasses G K,
      ∀ (E : Extension G K) (F : WeakAction G K), IsFiberAction E F →
        e (H2.mk F) = ExtClasses.mk E := by sorry
end GroupoidSchreier.Interpretation
