-- Prove2me | Theorems.Thm_KnodelPrimeCordial_labelF_cyc_bijective_mod0
-- name    : KnodelPrimeCordial.labelF_cyc_bijective_mod0
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-18T01:00:12.049273+00:00
-- url     : https://prove2.me/theorems/af216057-fb4f-4857-8303-954c0fef88f2
-- title:
--   The Lemma 2.3 labeling is a bijection in residue class $0$ modulo $12$
-- statement:
--   For every positive multiple of twelve, the explicit labeling $f$ used in the proof of Lemma 2.3 is a bijection from the vertices of the cyclic model onto $\{1,2,\dots,n\}$.
--
--   Let $f$ be the labeling of the paper *Prime cordial labeling of Knödel graph* (Haque, Khanam, Shahriar, 2026), proof of Lemma 2.3, defined on indices $0\le i\le n-1$ by
--
--   $$
--   f(v_i)=\begin{cases} i+2, & i\equiv 0,6,10 \pmod{12},\\ i+3, & i\equiv 1,2 \pmod{12},\\ i-2, & i\equiv 3 \pmod{12},\\ i-1, & i\equiv 4,8,11 \pmod{12},\\ i+1, & i\equiv 5 \pmod{12},\\ i+4, & i\equiv 7 \pmod{12},\\ i, & i\equiv 9 \pmod{12}. \end{cases}
--   $$
--
--   When $n$ is a positive multiple of twelve, the map $i\mapsto f(v_i)$ sends $\{0,\dots,n-1\}$ bijectively onto $\{1,\dots,n\}$.
--
--   **Role.** This is the bijectivity half of the prime-cordiality requirement. It is used together with the edge counts in residue class $0$ to establish prime cordiality there.
--
--   **Formalization Note** Indices are `Fin n` and the labeling is `labelF`. The conclusion is `Set.BijOn` onto `Set.Icc 1 n`. The proof rests on the block structure of `labelF`: on each block of twelve consecutive indices it shifts the block by one, mapping $[12q,12q+11]$ onto $[12q+1,12q+12]$.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026), proof of Lemma 2.3, p.4 (definition of f), and Table 2.1, Case 1 (n ≡ 0 mod 12), p.4

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

namespace KnodelPrimeCordial

theorem labelF_cyc_bijective_mod0 (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    Set.BijOn (fun i : Fin n => labelF i.val) Set.univ (Set.Icc 1 n) := by sorry

end KnodelPrimeCordial
