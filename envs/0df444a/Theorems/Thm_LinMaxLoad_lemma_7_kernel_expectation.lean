-- Prove2me | Theorems.Thm_LinMaxLoad_lemma_7_kernel_expectation
-- name    : LinMaxLoad.lemma_7_kernel_expectation
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T16:35:39.430271+00:00
-- url     : https://prove2.me/theorems/6bb82e62-9787-4666-bdef-313f92b335ad
-- title:
--   Proof of Lemma 7 — $\mathbb E_h[q^r] = \mathbb E_h[|\ker(h|_V)|] = 1 + (|V|-1)/n \le 2$
-- statement:
--   Let $K$ be a finite field with $q$ elements, $E$ a finite $K$-vector space, $V \le E$ a subspace, $h : E \to K^\ell$ a uniformly random linear map, $n = q^\ell$ and $r = \dim \ker(h|_V)$. Then
--
--   $$
--   \mathbb E_h[q^{r}] = \mathbb E_h\big[|\ker(h|_V)|\big] = \sum_{v \in V} \Pr_h[h(v) = 0] = 1 + \frac{|V| - 1}{n},
--   $$
--
--   and, when $\dim V \le \ell$ (so $|V| \le n$), this is at most $2$.
--
--   Averaging the conditional bound of Lemma 7 against this expectation gives the factor $2$ of Lemma 7.
--
--   Differences from the source:
--   - generalization: $\mathbb F_p^u$ and the field $\mathbb F_p$ → any finite $K$-module $E$ over any finite field $K$ ($q = |K|$); reason: the argument uses only linear algebra over a finite field; $K = \mathbb F_p$, $E = \mathbb F_p^u$ (`ZMod p`, `Fin u → ZMod p`) is the source statement
--   - encoding: $\le 2$ in the context of Lemma 7, whose standing hypothesis is $d = \dim V \le \ell$ → the clause `finrank V ≤ ℓ → … ≤ 2`; reason: Lemma 7's hypothesis stated as a binder; the equalities hold for every $V$
--   - encoding: $\sum_{v \in V}$ → `finsum` over the carrier of $V$; reason: Lean convention; $V$ is finite
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), proof of Lemma 7, kernel expectation, p.21

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinMaxLoad_probLin

namespace LinMaxLoad

/-- **Proof of Lemma 7, kernel expectation** (p.21 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
For `V ≤ E`, `h : E → K^ℓ` a uniformly random linear map, `r := dim ker(h|_V)`, `q = |K|`,
`n = q^ℓ`:
`E_h[q^r] = E_h[|ker(h|_V)|] = ∑_{v ∈ V} Pr[h(v) = 0] = 1 + (|V| − 1)/n`, and this is `≤ 2` when
`dim V ≤ ℓ`.

**Formalization Note** `E = F_p^u`, `K = F_p` on the page; here `K` is any finite field and `E`
any finite `K`-module. The sum over `V` is a `finsum` over the (finite) carrier of `V`. The
bound `≤ 2` is stated under Lemma 7's hypothesis `d = dim V ≤ ℓ` (i.e. `|V| ≤ n`). -/
theorem lemma_7_kernel_expectation {K E : Type*} [Field K] [Fintype K] [AddCommGroup E]
    [Module K E] [Finite E] (ℓ : ℕ) (V : Submodule K E) :
    avgLin K E ℓ (fun h => (Fintype.card K : ℝ) ^ Module.finrank K (LinearMap.ker (h.domRestrict V))) =
        avgLin K E ℓ (fun h => (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ)) ∧
      avgLin K E ℓ (fun h => (Nat.card (LinearMap.ker (h.domRestrict V)) : ℝ)) =
        ∑ᶠ v ∈ (V : Set E), probLin K E ℓ (fun h => h v = 0) ∧
      ∑ᶠ v ∈ (V : Set E), probLin K E ℓ (fun h => h v = 0) =
        1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ ℓ ∧
      (Module.finrank K V ≤ ℓ → 1 + ((Nat.card V : ℝ) - 1) / (Fintype.card K : ℝ) ^ ℓ ≤ 2) := by sorry

end LinMaxLoad
