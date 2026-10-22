-- Prove2me | Theorems.Thm_IoTFusion_KnownQuality_lemma_2
-- name    : IoTFusion.KnownQuality.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:20.585812+00:00
-- url     : https://prove2.me/theorems/835679f6-8fc2-4656-b13b-07b454a10545
-- title:
--   Lemma 2, p. 21 — once i's familiarity with j passes a fixed threshold, no sensor of quality below q_j/(1+ϵ) is targeted
-- statement:
--   Fix an instance of the model with $q_i > 0$ for every sensor and $v_{ij0}, w_{ij0} > 0$ for every pair. For every $\epsilon > 0$ there is a fixed threshold $\bar\psi_\epsilon \in \mathbb R$ such that, along every sample path $S_\infty$, for every sensor $i$, all sensors $j, j' \neq i$ and every period $t$:
--
--   $$\psi_{ijt}(s_{t-1}) > \bar\psi_\epsilon \ \text{ and } \ \frac{q_j}{q_{j'}} > 1 + \epsilon \quad\Longrightarrow\quad j^*_{it} \neq j'.$$
--
--   The point is that the threshold does not depend on $i$'s familiarity with $j'$: once $i$ is familiar enough with a sufficiently better sensor $j$, the worse sensor $j'$ is never targeted, however familiar $i$ is with it. This is the key step of the uniqueness half of Proposition 4.
--
--   **Formalization Note** The threshold depends only on the instance and $\epsilon$; it is chosen before the path, the sensors and the period. The paper's proof gives $[q_j^2(q_j^2/q_{j'}^2 - 1)]^{-1}$ for one pair (EC.79), which depends on $j, j'$; one threshold for the instance is the maximum over the finitely many pairs. Lean step $k$ is the paper's period $t = k+1$, so the familiarity value is $\psi_{ijt}(s_{t-1})$ at the state $s_k$.
-- source:
--   Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 21, Lemma 2 (proof pp. ec21–ec22, (EC.76)–(EC.82))

import Mathlib
import Definitions.Def_IoTFusion_KnownQuality_Model

namespace IoTFusion.KnownQuality

/-- **Lemma 2**, Saghafian, Tomlin, Biller, The Internet of Things and Information Fusion: Who Talks to Who?, SSRN 3124417 (version of October 16, 2020), p. 21.

For every `ε > 0` there is a fixed threshold `ψ̄_ε` such that, along every state path, for every
receiving sensor `i`, every pair `j, j' ≠ i` and every period, if `i`'s familiarity value with `j`
exceeds `ψ̄_ε` and `q_j / q_{j'} > 1 + ε`, then `i` does not target `j'` in that period.

**Formalization Note.** The instance is fixed first; the threshold depends only on the instance and
`ε`, and is uniform over paths, sensors and periods. The paper's proof ((EC.79), p. ec21 = PDF 54)
gives `[q_j^2 (q_j^2/q_{j'}^2 − 1)]^{-1}` for one pair; a single threshold for the instance is the
maximum over the finitely many pairs. Lean step `k` is the paper's period `t = k + 1`, so
`fam P i s k j (s k)` is `ψ_{ijt}(s_{t-1})` and `target P i s k` is `j*_{it}`. Hypotheses `hq`, `hv`,
`hw` are the paper's standing positivity assumptions (pp. 9–11). -/
theorem lemma_2 {n : ℕ} (P : Instance n) (hq : ∀ i, 0 < P.q i)
    (hv : ∀ i j, 0 < P.v i j) (hw : ∀ i j, 0 < P.w i j) :
    ∀ ε : ℝ, 0 < ε → ∃ ψbar : ℝ, ∀ (s : ℕ → ℝ) (i j j' : Fin n) (k : ℕ), j ≠ i → j' ≠ i →
      ψbar < fam P i s k j (s k) → 1 + ε < P.q j / P.q j' → target P i s k ≠ j' := by sorry

end IoTFusion.KnownQuality
