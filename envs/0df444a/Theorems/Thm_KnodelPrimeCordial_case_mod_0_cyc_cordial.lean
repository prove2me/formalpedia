-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_0_cyc_cordial
-- name    : KnodelPrimeCordial.case_mod_0_cyc_cordial
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-18T01:00:54.155585+00:00
-- url     : https://prove2.me/theorems/12060bec-b4a4-4421-a1db-a8ebe64ad9c7
-- title:
--   Prime cordiality of the cyclic model in residue class $0$ modulo $12$
-- statement:
--   In residue class $0$ modulo twelve, the Lemma 2.3 labeling is a prime cordial labeling of the cyclic model, with exactly $3n/4$ edges of each label.
--
--   Let $n\ge 12$ be a multiple of twelve and let $f$ be the labeling of Lemma 2.3. A prime cordial labeling of a finite simple graph on $N$ vertices is a bijection $f$ to $\{1,\dots,N\}$ such that, once every edge $uv$ is assigned label $0$ when $\gcd(f(u),f(v))>1$ and label $1$ when $\gcd(f(u),f(v))=1$, the two edge counts differ by at most one. The statement is that $f$ is such a labeling of the cyclic model $W_{3,n}$, and in fact the two counts are equal:
--
--   $$
--   e_0=e_1=\frac{3n}{4}.
--   $$
--
--   **Role.** This is Case 1 of the proof of Lemma 2.3. Transporting it along the cyclic model isomorphism gives prime cordiality of $W_{3,n}$ itself, which is the residue-class-$0$ branch of the mission.
--
--   **Formalization Note** The cyclic model is `cyc n` on `Fin n` and the labeling is `labelF`. Prime cordiality is `IsPrimeCordialLabeling`; its edge counts are `edgesLabelZero` and `edgesLabelOne`.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026), proof of Lemma 2.3, Case 1, pp.4-5 (and Table 2.1)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_labelF

namespace KnodelPrimeCordial

theorem case_mod_0_cyc_cordial (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    IsPrimeCordialLabeling (cyc n) (fun i : Fin n => labelF i.val) := by sorry

end KnodelPrimeCordial
