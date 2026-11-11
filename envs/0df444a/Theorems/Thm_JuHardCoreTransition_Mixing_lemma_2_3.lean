-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_2_3
-- name    : JuHardCoreTransition.Mixing.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:21.469791+00:00
-- url     : https://prove2.me/theorems/1b4fbbf8-dcab-4858-bdcd-97275b1d08f2
-- title:
--   Lemma 2.3 — covariance from marginal response, with sharpness
-- statement:
--   Let $\mu$ be a law on $\{0,1\}^V$ with $n=|V|\ge1$ and no deterministic coordinates; for $X\sim\mu$ put $p_v=\mu(X_v=1)$ and $p_{\max}=\max_vp_v$. Fix $0<\alpha<1$, $L\ge1$, $h_0>0$ and $u\in[0,1]$. Suppose that for every $0<h\le h_0$, every field tilt $\psi\in[e^{-h},e^h]^V$ and every $v\in V$,
--   $$|(\psi*\mu)(X_v=1)-\mu(X_v=1)|\le Lp_{\max}(\sqrt u+h^\alpha).$$
--   Then there is a constant $C=C(L,h_0,\alpha)$ such that
--   $$\mathrm{Cov}_\mu(X)\preceq Cp_{\max}\Big[1+(np_{\max})^{\frac{1-\alpha}{1+\alpha}}+np_{\max}u\Big]I_n .$$
--
--   The dependence on $n,p_{\max},u$ is optimal up to constants, already for equal marginals $0<p\le1/2$. As specified by the cited Proposition 4.5, for every such $n,p,u$ there is a full-support law with every marginal $p$, response at most $6p(\sqrt u+h^\alpha)$ for $0<h\le1$, and largest covariance eigenvalue at least $\frac p8[1+(np)^{(1-\alpha)/(1+\alpha)}+npu]$.
--
--   Differences from the source:
--   - encoding: a law on {0,1}^V with |V| = n → a Boolean law on Fin n; reason: relabel V; C depends only on L, h₀, α, so it is stated before n, μ and u
--   - encoding: Cov_μ(X) ⪯ M I_n → zᵀ Cov_μ(X) z ≤ M Σ z_v² for every real z; reason: definition of the PSD order
--   - encoding: p_max = max_v p_v → ⨆ over Fin n of the marginals (a maximum, n ≥ 1); reason: finite nonempty index set
--   - encoding: optimal dependence on n, p_max, u, already for equal marginals p_max ≤ 1/2; see Proposition 4.5 → a full-support witness for each n ≥ 1, 0 < p ≤ 1/2 and u ∈ [0,1], with response constant 6, cutoff 1 and covariance lower coefficient 1/8; reason: Proposition 4.5 (printed p.23 / PDF p.24) supplies the precise witnesses for the sharpness sentence on p.9; the lower eigenvalue bound is expressed by a unit-vector Rayleigh quotient
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 2.3, printed p.9 / PDF p.10; sharpness witnesses: Proposition 4.5, printed p.23 / PDF p.24

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_BooleanLaws

namespace JuHardCoreTransition.Mixing

/-- **Lemma 2.3 (Covariance from marginal response)** (printed p.9 / PDF p.10). Let `μ` be a law
on `{0,1}^V` with `n = |V| ≥ 1` and no deterministic coordinates; `p_v = μ(X_v = 1)`,
`p_max = max_v p_v`. Fix `0 < α < 1`, `L ≥ 1`, `h₀ > 0` and `u ∈ [0, 1]`. If for every
`0 < h ≤ h₀`, every field tilt `ψ ∈ [e^{−h}, e^h]^V` and every `v`,
`|(ψ ∗ μ)(X_v = 1) − μ(X_v = 1)| ≤ L p_max(√u + h^α)`, then
`Cov_μ(X) ⪯ C p_max [1 + (n p_max)^{(1−α)/(1+α)} + n p_max u] I_n` with `C = C(L, h₀, α)`.
The dependence on `n, p_max, u` is optimal up to constants, already for equal marginals
`p ≤ 1/2`: the second conjunct spells out the witnesses in Proposition 4.5 (printed p.23 /
PDF p.24), with response constant `6`, field cutoff `1`, and covariance coefficient `1/8`.
(`V = Fin n`; PSD order and the largest covariance eigenvalue are expressed by quadratic forms.) -/
theorem lemma_2_3 (α L h₀ : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hL : 1 ≤ L) (hh₀ : 0 < h₀) :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ μ : Finset (Fin n) → ℝ, IsBoolLaw μ →
      NoDeterministic μ → ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        (∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ ψ : Fin n → ℝ,
          (∀ v, Real.exp (-h) ≤ ψ v ∧ ψ v ≤ Real.exp h) → ∀ v : Fin n,
            |marg (tilt ψ μ) v - marg μ v| ≤
              L * (⨆ w : Fin n, marg μ w) * (Real.sqrt u + h ^ α)) →
        ∀ z : Fin n → ℝ,
          covQuad μ z ≤
            C * (⨆ w : Fin n, marg μ w) *
              (1 + ((n : ℝ) * (⨆ w : Fin n, marg μ w)) ^ ((1 - α) / (1 + α)) +
                (n : ℝ) * (⨆ w : Fin n, marg μ w) * u) * ∑ v, z v ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ p u : ℝ, 0 < p → p ≤ 1 / 2 → 0 ≤ u → u ≤ 1 →
      ∃ μ : Finset (Fin n) → ℝ, IsBoolLaw μ ∧ (∀ I, 0 < μ I) ∧
        (∀ v, marg μ v = p) ∧
        (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ ψ : Fin n → ℝ,
          (∀ v, Real.exp (-h) ≤ ψ v ∧ ψ v ≤ Real.exp h) → ∀ v : Fin n,
            |marg (tilt ψ μ) v - p| ≤ 6 * p * (Real.sqrt u + h ^ α)) ∧
        ∃ z : Fin n → ℝ, (∑ v, z v ^ 2) = 1 ∧
          p / 8 * (1 + ((n : ℝ) * p) ^ ((1 - α) / (1 + α)) + (n : ℝ) * p * u) ≤
            covQuad μ z) := by sorry

end JuHardCoreTransition.Mixing
