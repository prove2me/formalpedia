-- Prove2me | Theorems.Thm_KaimanovichVershik_exists_typical_finset_of_hasFiniteEntropy
-- name    : KaimanovichVershik.exists_typical_finset_of_hasFiniteEntropy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-05T22:31:26.305987+00:00
-- url     : https://prove2.me/theorems/2ac8a41a-dbc1-431a-9197-0f813ac315b9
-- title:
--   Kaimanovich–Vershik (as Erschler–Zheng apply it, p. 11) — Shannon's theorem: μ^(n) puts mass ⩾ 1 − ε on a finite set where e^(−n(h+ε)) ⩽ μ^(n) ⩽ e^(−n(h−ε))
-- statement:
--   Let $\Gamma$ be a countable group and $\mu$ a probability on $\Gamma$ (`IsProbability`) of finite entropy (`HasFiniteEntropy`), and let $\mathbf h = $ `asymptoticEntropy μ`. For every $\varepsilon > 0$ there is $N$ such that for every $n > N$ there is a finite set $V \subseteq \Gamma$ with
--   $$\mu^{(n)}(V) \ge 1 - \varepsilon \qquad\text{and}\qquad e^{-n(\mathbf h + \varepsilon)} \le \mu^{(n)}(x) \le e^{-n(\mathbf h - \varepsilon)} \quad\text{for every } x \in V,$$
--   where $\mu^{(n)}$ is the $n$-th convolution power (`convPow`) and $\mu^{(n)}(V)$ its mass on $V$ (`mass`).
--
--   Erschler and Zheng, p. 11: “By Shannon’s theorem, for any $\epsilon > 0$, there exists a constant $N_\epsilon$ such that for any $n > N_\epsilon$, there is a finite set $V_n \subset G$ such that $\mu^{(n)}(V_n) \geqslant 1 - \epsilon$ and $e^{-n(\mathbf h + \epsilon)} \leqslant \mu^{(n)}(x) \leqslant e^{-n(\mathbf h - \epsilon)}$ for $x \in V_n$.”
--
--   Here $\mathbf h$ is “the asymptotic entropy of $\mu$” (p. 11) and $G$ is the group $\Gamma$. The sentence is in the proof of Lemma 2.1, where $\mu$ also has a non-trivial Poisson boundary; the statement does not assume that.
-- source:
--   Kaimanovich, V. A. and Vershik, A. M., Random walks on discrete groups: boundary and entropy, Ann. Probab. 11 (1983) 457–490, https://doi.org/10.1214/aop/1176993497, p. 11, the Shannon theorem, as applied in Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 11

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
open ErschlerZheng

namespace KaimanovichVershik

theorem exists_typical_finset_of_hasFiniteEntropy {Γ : Type*} [Group Γ] [Countable Γ]
    (μ : Γ → ℝ) (hμ : IsProbability μ) (hH : HasFiniteEntropy μ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, ∃ V : Finset Γ, 1 - ε ≤ mass (convPow μ n) (V : Set Γ) ∧
      ∀ x ∈ V, Real.exp (-(n * (asymptoticEntropy μ + ε))) ≤ convPow μ n x ∧
        convPow μ n x ≤ Real.exp (-(n * (asymptoticEntropy μ - ε))) := by
  sorry

end KaimanovichVershik
