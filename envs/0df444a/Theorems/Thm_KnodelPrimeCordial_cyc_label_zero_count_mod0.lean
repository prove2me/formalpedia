-- Prove2me | Theorems.Thm_KnodelPrimeCordial_cyc_label_zero_count_mod0
-- name    : KnodelPrimeCordial.cyc_label_zero_count_mod0
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-18T01:27:08.408858+00:00
-- url     : https://prove2.me/theorems/3b8e9f9d-a622-4755-bc97-b962294e2ada
-- title:
--   Edges labelled $0$ in the cyclic model, residue class $0$ modulo $12$
-- statement:
--   In residue class $0$ modulo twelve, exactly three quarters of the edges of the cyclic model receive label $0$.
--
--   Let $n\ge 12$ be a multiple of twelve and let $f$ be the labeling of the proof of Lemma 2.3. The cyclic model $W_{3,n}$ has $3n/2$ edges: the $n$ cycle edges $v_iv_{i+1}$ and the $n/2$ chords $v_{2i}v_{2i+5}$, all indices read modulo $n$. Assign to each edge $uv$ the label $0$ when $\gcd(f(u),f(v))>1$ and the label $1$ when $\gcd(f(u),f(v))=1$. The claim is that
--
--   $$
--   e_0 \;=\; \#\{uv\in E : \gcd(f(u),f(v))>1\} \;=\; \frac{3n}{4}.
--   $$
--
--   **Role.** This is one half of the prime-cordiality condition in residue class $0$. Together with the corresponding count $e_1=3n/4$ it gives $e_0=e_1$, which is stronger than the required $|e_0-e_1|\le 1$.
--
--   **Formalization Note** The graph is `cyc n` on `Fin n` and the edge set is `edgesLabelZero (cyc n) f`, a `Finset` of unordered pairs. The count covers cycle edges and chords at once, so no case split on the two edge families is needed at this level.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026), proof of Lemma 2.3, Case 1, pp.4-5: 'there are 3n/4 edges labeled with 0 and 3n/4 edges labeled with 1 in total under f0'

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

namespace KnodelPrimeCordial

theorem cyc_label_zero_count_mod0 (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    (edgesLabelZero (cyc n) (fun i : Fin n => labelF i.val)).card = 3 * n / 4 := by sorry

end KnodelPrimeCordial
