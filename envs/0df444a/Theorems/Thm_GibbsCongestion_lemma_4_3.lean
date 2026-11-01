-- Prove2me | Theorems.Thm_GibbsCongestion_lemma_4_3
-- name    : GibbsCongestion.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:02:20.633339+00:00
-- url     : https://prove2.me/theorems/a53eec7d-8351-4605-808d-0f04e2daf97a
-- title:
--   Lemma 4.3: the load-profile generating polynomial is strongly log-concave
-- statement:
--   Throughout, $\Gamma$ is an extension parallel congestion game with common strategy set $\mathcal P$ (the $o,d$-paths of an EP network), $n\ge1$ players and non-negative, non-decreasing costs $c_e$; $T\ge0$ is the temperature, $\Phi$ is Rosenthal's potential, $\pi$ the Gibbs distribution, and $P$ the relaxed logit dynamics (with probability $\tfrac12$ two random distinct players swap strategies, with probability $\tfrac12$ a logit step).
--
--   The $n$-homogeneous generating polynomial, with one variable $x_p$ per path $p\in\mathcal P$,
--   $$g(x)=\sum_{\alpha\in\mathcal L}|\mathcal S(\alpha)|\,e^{-T\Phi(\alpha)}x^\alpha=\sum_{\alpha\in\mathcal L}\frac{n!}{\alpha!}e^{-T\Phi(\alpha)}x^\alpha\qquad(11)$$
--   is strongly log-concave. Hence the distribution $\pi'$ on $\mathcal L$ given by $\pi'(\alpha)\propto\frac{n!}{\alpha!}e^{-T\Phi(\alpha)}$ is strongly log-concave.
--
--   The statement has four parts: the two forms of (11) agree, that is $|\mathcal S(\alpha)|=n!/\alpha!$ for $\alpha\in\mathcal L$ (p.15); $g$ is homogeneous of degree $n$; $g$ is SLC; the generating polynomial $\sum_\alpha\pi'(\alpha)x^\alpha$ of $\pi'$ is SLC (the definition of an SLC distribution, p.9). Its polarization is the generating polynomial of the base-exchange chain compared with the projection chain in (14).
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: L = {α ∈ [q]ⁿ : |α| = n} → L = {α : P → ℕ | Σ_p α_p = n}; reason: the set is used as the set of strategy load profiles (one coordinate per path)
--   - reading: g(x₁, …, xₙ) and log-concavity on an unspecified S → one variable x_p per path p ∈ P; log-concavity on the open positive orthant; reason: α is indexed by paths; open orthant is the cited works' convention
--   - encoding: Φ(α) = Φ(s) for s ∈ S(α) (p.15, footnote 21) → loadPotential, the formula Σ_e Σ_{k=1}^{Σ_{p∋e} α_p} c_e(k); reason: ℓ_e(s) = Σ_{p∋e} z_p(s), so the formula takes the value Φ(s) on every s ∈ S(α)
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Lemma 4.3, display (11), p.15

import Mathlib
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_loadProfiles
import Definitions.Def_GibbsCongestion_strategyLoad
import Definitions.Def_GibbsCongestion_loadPotential
import Definitions.Def_GibbsCongestion_IsSLC

namespace GibbsCongestion

/-- **Lemma 4.3** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Lemma 4.3, display (11), p.15). The `n`-homogeneous generating
polynomial
`g(x) = ∑_{α ∈ L} |S(α)| e^{−TΦ(α)} x^α = ∑_{α ∈ L} (n!/α!) e^{−TΦ(α)} x^α`
(one variable `x_p` per path `p ∈ P`) is strongly log-concave. Hence the distribution `π'` on `L`
with `π'(α) ∝ (n!/α!) e^{−TΦ(α)}` is strongly log-concave.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). The four conjuncts are: the two forms of (11) agree, `|S(α)| = n!/α!` for `α ∈ L` (p.15); `g` is
`n`-homogeneous; `g` is SLC; the generating polynomial `∑_α π'(α) x^α` of `π'` is SLC (the definition
of an SLC distribution, p.9). -/
theorem lemma_4_3 {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) (T : ℝ) (hT : 0 ≤ T) :
    (∀ α ∈ loadProfiles P n,
      (((Finset.univ : Finset (Fin n → P)).filter (fun s => strategyLoad s = α)).card : ℝ) =
        (n.factorial : ℝ) / (∏ p, ((α p).factorial : ℝ))) ∧
    (∑ α ∈ loadProfiles P n, MvPolynomial.C ((n.factorial : ℝ) / (∏ p, ((α p).factorial : ℝ)) *
        Real.exp (-T * loadPotential c α)) * ∏ p, MvPolynomial.X p ^ α p).IsHomogeneous n ∧
    IsSLC (∑ α ∈ loadProfiles P n, MvPolynomial.C ((n.factorial : ℝ) / (∏ p, ((α p).factorial : ℝ)) *
        Real.exp (-T * loadPotential c α)) * ∏ p, MvPolynomial.X p ^ α p) ∧
    IsSLC (∑ α ∈ loadProfiles P n, MvPolynomial.C
        (((n.factorial : ℝ) / (∏ p, ((α p).factorial : ℝ)) * Real.exp (-T * loadPotential c α)) /
          ∑ β ∈ loadProfiles P n, (n.factorial : ℝ) / (∏ p, ((β p).factorial : ℝ)) *
            Real.exp (-T * loadPotential c β)) * ∏ p, MvPolynomial.X p ^ α p) := by sorry

end GibbsCongestion
