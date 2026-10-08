-- Prove2me | Theorems.Thm_MetricGenerators_FewComponents_matching_join
-- name    : MetricGenerators.FewComponents.matching_join
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:21.151875+00:00
-- url     : https://prove2.me/theorems/9449aaf2-6af3-46d5-8d23-62281f26ddca
-- title:
--   Proof of Theorem 5, p. 391: a matching M indexes Z, and ⋃{mw, mx, my, mz_m} is a minimum T-join with q components
-- statement:
--   Let $G$ and $T$ be built from an instance $(W,X,Y,H)$ of 3DM with $|W|=|X|=|Y|=q$, and let $M\subseteq H$ be a matching. Then:
--
--   1. $Z$ can be indexed with $M$, that is, there is a bijection $M\to Z$, $m\mapsto z_m$;
--   2. for **every** such indexing, the edge set
--
--   $$F_M=\bigcup\big\{\{mw,\ mx,\ my,\ mz_m\} : m=(w,x,y)\in M\big\}$$
--
--   is a minimum $T$-join of $G$ with exactly $q$ connected components.
--
--   This is the direction "matching $\Rightarrow$ minimum $T$-join with at most $q$ components" of the Claim in the proof of Theorem 5.
--
--   **Formalization Note.** Since $Z$ is a copy of $\{0,\dots,q-1\}$, the indexing is a bijection $\sigma:M\to\{0,\dots,q-1\}$ with $z_m=(3,\sigma(m))$. Components are those of the graph $(V(F),F)$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.1, proof of Theorem 5, second paragraph after the Claim

import Mathlib
import Definitions.Def_MetricGenerators_FewComponents_TJoin
import Definitions.Def_MetricGenerators_FewComponents_ThreeDM
import Definitions.Def_MetricGenerators_FewComponents_Gadget

namespace MetricGenerators.FewComponents

/-- A matching gives a minimum `T`-join with `q` components (Sebő and Tannier, On Metric
Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), §3.1, proof of Theorem 5, p. 391,
unnumbered): "If M is a matching, then Z can be indexed with M: Z = {z_m : m ∈ M}. Now
⋃{{mw, mx, my, mz_m} : m = (w, x, y) ∈ M} is a minimum T-join with q components."

**Formalization Note.** "`Z` can be indexed with `M`" is the first conjunct: there is a
bijection `M ≃ Fin q` (`Z` is the class `3` copy of `Fin q`). The second conjunct holds for
**every** such indexing `σ`, `z_m = (3, σ m)`; `matchingJoin M hMH σ` is the displayed union.
Components are those of the graph `(V(F), F)` (`numComponents`). -/
theorem matching_join (q : ℕ) (H : Finset (Fin q × Fin q × Fin q))
    (M : Finset (Fin q × Fin q × Fin q)) (hMH : M ⊆ H) (hM : IsMatching q M) :
    Nonempty (↥M ≃ Fin q) ∧
      ∀ σ : ↥M ≃ Fin q,
        IsMinTJoin (gadget q H) (gadgetT q H) (matchingJoin M hMH σ) ∧
          numComponents (matchingJoin M hMH σ) = q := by sorry

end MetricGenerators.FewComponents
