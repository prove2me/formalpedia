-- Prove2me | Theorems.Thm_KnodelPrimeCordial_lemma_2_3_case_1
-- name    : KnodelPrimeCordial.lemma_2_3_case_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:01:57.805454+00:00
-- url     : https://prove2.me/theorems/fb5ee7ee-c5d1-41f8-991a-6d8f37fbe91e
-- title:
--   Lemma 2.3, Case 1 — for $n\equiv 0 \pmod{12}$, $f_0=f$ is prime cordial with $3n/4$ edges of each label
-- statement:
--   Let $n>0$ with $n\equiv 0\pmod{12}$, and let $f_0(v_i)=f(v_i)$ for $0\le i\le n-1$, where $f$ is the residue-mod-$12$ labeling of the proof of Lemma 2.3. Then:
--
--   1. $f_0$ is a bijection from $\{v_0,\dots,v_{n-1}\}$ onto $\{1,2,\dots,n\}$;
--   2. exactly $3n/4$ edges of $W_{3,n}$ are labeled $0$ and exactly $3n/4$ edges are labeled $1$ under $f_0$:
--
--   $$
--   \#\{uv:\gcd(f_0(u),f_0(v))>1\}=\#\{uv:\gcd(f_0(u),f_0(v))=1\}=\tfrac{3n}{4};
--   $$
--
--   3. hence $f_0$ is a prime cordial labeling of $W_{3,n}$.
--
--   Clauses 1 and 2 are stated on the paper's vertex names $v_i$, i.e. on the cyclic model ($n$-cycle plus the chords $v_{2i}v_{2i+5}$); clause 3 states the conclusion on the Knödel graph $W_{3,n}$ itself, for the labeling of the pair vertices $(i,j)$ that gives $v_i$ the label $f(v_i)$. This is the one case of Lemma 2.3 that the paper verifies in full.
--
--   Differences from the source:
--   - encoding: n ≡ 0 (mod 12) (with W(3, n), so n ≥ 12) → hypotheses 0 < n and 12 ∣ n; reason: the same set of n
--   - encoding: bijection and edge counts on V(W(3, n)) written through the names v_i → clauses 1–2 on the cyclic model cyc n over Fin n; reason: the paper's p.3 identification (milestone cyclic_model); clause 3 restates the conclusion on knodel 3 n
--   - encoding: f0 on the vertices of W(3, n) → in clause 3, a labeling g of Fin 2 × Fin (n/2) with g(v_i) = f(i) for every i; reason: v_i ranges over all vertices, so g is the paper's f0 and is unique
--   - encoding: vertex (i, j) with i = 1, 2 → Fin 2 × Fin (n/2) with sides 1, 2 as 0, 1; reason: Lean convention; same graph
--   - encoding: bijection f from V to {1, …, |V|} → f : V → ℕ with Set.BijOn f univ (Icc 1 |V|); reason: Lean convention; same labelings
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), proof of Lemma 2.3, Case 1, pp.4–5 (PDF pp.4–5); conclusion p.5

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_vtx
import Definitions.Def_KnodelPrimeCordial_labelF

namespace KnodelPrimeCordial

/-- **Lemma 2.3, Case 1** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel graph*,
manuscript (2026), proof of Lemma 2.3, Case 1, pp.4–5): "Case 1. n ≡ 0 (mod 12). Let
f0(vi) = f(vi) for 0 ≤ i ≤ n − 1. One can easily verify that f0 is a bijection from V(W(3, n))
to {1, 2, . . . , n}." … "Therefore, there are 3n/4 edges labeled with 0 and 3n/4 edges labeled
with 1 in total under f0 defined in Table 2.1, i.e, f0 is a prime cordial labeling of W(3, n)
for n ≡ 0 mod 12."

For every `n > 0` with `12 ∣ n`, the labeling `f0(v_i) = f(i)` (`labelF`):
1. maps `{v_0, …, v_{n−1}}` bijectively onto `{1, …, n}`;
2. labels exactly `3n/4` edges of the cyclic model `0` and exactly `3n/4` edges `1`;
3. transported to the pair vertices `(i, j)` of `W_{3,n}` through the paper's names `v_i`
   (`vtx`), is a prime cordial labeling of `W_{3,n}`.

**Formalization Note** Clauses 1–2 are stated on the paper's own vertex names `v_i`
(`cyc n` on `Fin n`); clause 3 states the conclusion on `knodel 3 n` itself, for the labeling
`g` with `g(v_i) = f(i)` (unique, since `vtx` is a bijection). -/
theorem lemma_2_3_case_1 (n : ℕ) (hn : 0 < n) (h12 : 12 ∣ n) :
    Set.BijOn (fun i : Fin n => labelF i.val) Set.univ (Set.Icc 1 n) ∧
      (edgesLabelZero (cyc n) (fun i : Fin n => labelF i.val)).card = 3 * n / 4 ∧
      (edgesLabelOne (cyc n) (fun i : Fin n => labelF i.val)).card = 3 * n / 4 ∧
      ∃ g : Fin 2 × Fin (n / 2) → ℕ, (∀ i : Fin n, g (vtx n (by omega) i) = labelF i.val) ∧
        IsPrimeCordialLabeling (knodel 3 n) g := by sorry

end KnodelPrimeCordial
