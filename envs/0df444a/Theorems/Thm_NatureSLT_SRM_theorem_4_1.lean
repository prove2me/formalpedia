-- Prove2me | Theorems.Thm_NatureSLT_SRM_theorem_4_1
-- name    : NatureSLT.SRM.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:48.369897+00:00
-- url     : https://prove2.me/theorems/b004148d-1bdc-439c-9f7c-887570486242
-- title:
--   Theorem 4.1 — structural risk minimization converges to the smallest risk with asymptotic rate r_{n(ℓ)} + T_{n(ℓ)} √(h_{n(ℓ)} ln ℓ / ℓ)
-- statement:
--   Let $F$ be a probability measure on a set $Z$ and $S = \{Q(z, \alpha),\ \alpha \in \Lambda\}$ a nonempty set of measurable, integrable, nonnegative functions on $Z$, indexed by an arbitrary parameter set $\Lambda$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ for the risk and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for the empirical risk on an i.i.d. sample $z_1, \dots, z_\ell$ from $F$.
--
--   **Structure.** $S$ carries a structure of nested subsets $S_k = \{Q(z, \alpha),\ \alpha \in \Lambda_k\}$, $S_1 \subset S_2 \subset \cdots \subset S_n \subset \cdots$ (4.3), each nonempty, which is admissible with constants $T_k$: each $S_k$ has a finite VC dimension $h_k$, and either
--
--   - (i) every element consists of totally bounded functions, $0 \le Q(z, \alpha) \le B_k$ for $\alpha \in \Lambda_k$, and $T_k = B_k$ ($h_k$ the VC dimension of $S_k$ as a set of real functions with $\beta \in (0, B_k)$); or
--   - (ii) for a fixed $p > 2$ every element satisfies (4.4), $\sup_{\alpha \in \Lambda_k} \left(\int Q^p(z,\alpha)\, dF(z)\right)^{1/p} / \int Q(z,\alpha)\, dF(z) \le \tau_k$, and $T_k = \tau_k$ ($h_k$ the VC dimension with $\beta \in (0, \infty)$).
--
--   The union $S^* = \bigcup_k S_k$ is everywhere dense in $S$ in the metric $\rho(Q(z,\alpha_1), Q(z,\alpha_2)) = \int |Q(z,\alpha_1) - Q(z,\alpha_2)|\, dF(z)$: for every $\alpha \in \Lambda$ and $\varepsilon > 0$ some $\beta \in \Lambda_k$, for some $k$, has $\rho(Q(z,\alpha), Q(z,\beta)) \le \varepsilon$.
--
--   **SRM.** A law $n = n(\ell)$ (4.5) chooses the element $S_{n(\ell)}$ in which the empirical risk is minimized, and $Q(z, \alpha^{n(\ell)}_\ell)$, $\alpha^{n(\ell)}_\ell \in \Lambda_{n(\ell)}$, is a function minimizing the empirical risk over $S_{n(\ell)}$ (for every sample). Let
--   $$R(\alpha_0) = \inf_{\alpha \in \Lambda} \int Q(z, \alpha)\, dF(z), \qquad r_n = \inf_{\alpha \in \Lambda_n} \int Q(z,\alpha)\, dF(z) - \inf_{\alpha\in\Lambda} \int Q(z,\alpha)\, dF(z) \quad (4.8),$$
--   the smallest risk and the rate of approximation, and
--   $$V(\ell) = r_{n(\ell)} + T_{n(\ell)} \sqrt{\frac{h_{n(\ell)} \ln \ell}{\ell}} \qquad (4.6).$$
--
--   **Theorem.** If the law $n = n(\ell)$ satisfies
--   $$\lim_{\ell \to \infty} \frac{T^2_{n(\ell)}\, h_{n(\ell)} \ln \ell}{\ell} = 0, \qquad (4.7)$$
--   then the sequence of risks $R(\alpha^{n(\ell)}_\ell)$ converges in probability to the smallest risk $R(\alpha_0)$, and it converges to $R(\alpha_0)$ with asymptotic rate $V(\ell)$: there is a constant $C$ such that $V^{-1}(\ell)\, |R(\alpha^{n(\ell)}_\ell) - R(\alpha_0)| \to C$ in probability as $\ell \to \infty$ (the book's definition of an asymptotic rate, footnote 3, p. 97).
--
--   This is the asymptotic justification of the structural risk minimization principle: by choosing the element of the structure as a function of the sample size, one trades the approximation error $r_{n(\ell)}$ against the confidence term $T_{n(\ell)}\sqrt{h_{n(\ell)} \ln \ell/\ell}$.
--
--   **Formalization Note** The structure is indexed by $k \in \mathbb N = \{0, 1, \dots\}$ (the book starts at $1$; a shift of index changes nothing). The empirical minimizer is a given map from samples to $\Lambda_{n(\ell)}$, with $R(\alpha^{n(\ell)}_\ell)$ assumed a measurable function of the sample (the book's measurability conditions); its existence is not claimed. Functions are nonnegative throughout (the book's setting of bounded nonnegative and unbounded nonnegative losses). The ratio in (4.4) is written multiplied out, with $Q^p$ assumed integrable. The infima are over nonempty sets of reals bounded below by $0$, so they are genuine. Convergence in probability is $\lim_\ell F^\ell\{|R(\alpha^{n(\ell)}_\ell) - R(\alpha_0)| > \varepsilon\} = 0$ for every $\varepsilon > 0$. The rate is the book's literal footnote-3 definition (convergence in probability of the normalized error to a constant), stronger than the usual $O_P(V(\ell))$ reading; where $V(\ell) = 0$ Lean reads $V^{-1}(\ell) = 0$. The page does not require $n(\ell) \to \infty$, and none is added: as printed, a law that keeps returning to a small element of the structure satisfies (4.7) while the risks fail to converge (finding F1); the item is stated as printed.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 97–98, Theorem 4.1, Eqs. (4.3)–(4.8)

import Mathlib
import Definitions.Def_NatureSLT_SRM_vcDimReal
import Definitions.Def_NatureSLT_SRM_ConvergesWithRate

open MeasureTheory Filter Topology

namespace NatureSLT.SRM

/-- **Theorem 4.1** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., pp. 97–98).
Setting (§4.1–4.2, pp. 94–97): a set `S` of measurable, integrable, nonnegative functions
`Q(z, α)`, `α ∈ Λ`; an admissible structure of nested subsets `S_k = {Q(z, α), α ∈ Λ_k}`
(4.3), each nonempty with finite VC dimension `h_k`, and either (i) all elements totally bounded,
`0 ≤ Q ≤ T_k = B_k` on `S_k` (`h_k` the VC dimension with `β ∈ (0, B_k)`), or (ii) all elements
satisfying (4.4), `(∫ Q^p dF)^{1/p} ≤ T_k ∫ Q dF` on `S_k` for a fixed `p > 2`, `T_k = τ_k`
(`h_k` the VC dimension with `β ∈ (0, ∞)`); `S* = ⋃ S_k` everywhere dense in `S` in the metric
`ρ(Q₁, Q₂) = ∫ |Q₁ − Q₂| dF`. For a law `n = n(ℓ)` (4.5) satisfying (4.7)
`T²_{n(ℓ)} h_{n(ℓ)} ln ℓ / ℓ → 0`, let `α^{n(ℓ)}_ℓ` minimize the empirical risk over
`Λ_{n(ℓ)}`. Then `R(α^{n(ℓ)}_ℓ)` converges (in probability) to `R(α₀) = inf_{α ∈ Λ} R(α)`
with asymptotic rate (footnote 3) `V(ℓ) = r_{n(ℓ)} + T_{n(ℓ)} √(h_{n(ℓ)} ln ℓ / ℓ)` (4.6),
where `r_n = inf_{Λ_n} R − inf_Λ R` (4.8). -/
theorem theorem_4_1 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Nonempty Λ] (Q : Λ → Z → ℝ) (hQ0 : ∀ α z, 0 ≤ Q α z)
    (hQmeas : ∀ α, Measurable (Q α)) (hQint : ∀ α, Integrable (Q α) F)
    (Λs : ℕ → Set Λ) (hnest : Monotone Λs) (hne : ∀ k, (Λs k).Nonempty)
    (hdense : ∀ α : Λ, ∀ ε : ℝ, 0 < ε → ∃ k, ∃ β ∈ Λs k, ∫ z, |Q α z - Q β z| ∂F ≤ ε)
    (h : ℕ → ℕ) (T : ℕ → ℝ)
    (hcase :
      (∀ k, (∀ α ∈ Λs k, ∀ z, Q α z ≤ T k) ∧
        vcDimReal (fun α : Λs k => Q α) 0 ((T k : ℝ) : EReal) = h k) ∨
      (∃ p : ℝ, 2 < p ∧ ∀ k,
        (∀ α ∈ Λs k, Integrable (fun z => Q α z ^ p) F ∧
          (∫ z, Q α z ^ p ∂F) ^ (1 / p) ≤ T k * ∫ z, Q α z ∂F) ∧
        vcDimReal (fun α : Λs k => Q α) 0 ⊤ = h k))
    (n : ℕ → ℕ)
    (h47 : Tendsto (fun ℓ : ℕ => T (n ℓ) ^ 2 * h (n ℓ) * Real.log ℓ / ℓ) atTop (𝓝 0))
    (αhat : ∀ ℓ : ℕ, (Fin ℓ → Z) → Λ) (hαmem : ∀ ℓ z, αhat ℓ z ∈ Λs (n ℓ))
    (herm : ∀ ℓ (z : Fin ℓ → Z), ∀ α ∈ Λs (n ℓ),
      (1 / (ℓ : ℝ)) * ∑ i, Q (αhat ℓ z) (z i) ≤ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i))
    (hαmeas : ∀ ℓ, Measurable (fun z : Fin ℓ → Z => ∫ x, Q (αhat ℓ z) x ∂F)) :
    let R : Λ → ℝ := fun α => ∫ z, Q α z ∂F
    let R₀ : ℝ := ⨅ α, R α
    let r : ℕ → ℝ := fun k => (⨅ α : Λs k, R α) - R₀
    let V : ℕ → ℝ := fun ℓ => r (n ℓ) + T (n ℓ) * Real.sqrt (h (n ℓ) * Real.log ℓ / ℓ)
    (∀ ε : ℝ, 0 < ε → Tendsto (fun ℓ : ℕ => (Measure.pi fun _ : Fin ℓ => F)
      {z | ε < |R (αhat ℓ z) - R₀|}) atTop (𝓝 0)) ∧
    ConvergesWithRate F (fun ℓ z => R (αhat ℓ z)) R₀ V := by sorry

end NatureSLT.SRM
