-- Prove2me | Theorems.Thm_GibbsCongestion_proposition_4_1
-- name    : GibbsCongestion.proposition_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:01:24.490109+00:00
-- url     : https://prove2.me/theorems/4d0508e4-35cd-486f-865a-d45c84c78c61
-- title:
--   Proposition 4.1 (Fujishige et al.): Rosenthal's potential on load profiles is M-convex
-- statement:
--   Let $\Gamma$ be an extension parallel congestion game with common strategy set $\mathcal P$, $n\ge1$ players and non-negative, non-decreasing costs. Then Rosenthal's potential on strategy load profiles,
--   $$\Phi:\mathcal L\to\mathbb R,\qquad\Phi(\alpha)=\Phi(s)\ \text{ for } s\in\mathcal S(\alpha),$$
--   is **M-convex**: extended by $+\infty$ outside $\mathcal L=\{\alpha\in\mathbb Z^{\mathcal P}_{\ge0}:\sum_p\alpha_p=n\}$, it satisfies the exchange axiom: for all $\alpha,\beta\in\mathcal L$ and every $p$ with $\alpha_p>\beta_p$ there is $p'$ with $\alpha_{p'}<\beta_{p'}$ and
--   $$\Phi(\alpha)+\Phi(\beta)\ \ge\ \Phi(\alpha-e_p+e_{p'})+\Phi(\beta+e_p-e_{p'}).$$
--
--   This is what makes the load-profile generating polynomial (11) strongly log-concave (Lemma 4.3).
--
--   **Formalization Note** M-convexity is Murota's exchange axiom M-EXC[$\mathbb Z$] (the published definition `MExchangeAxiom`) for a function $\mathbb Z^{\mathcal P}\to\mathbb R\cup\{+\infty\}$; with a nonempty domain it forces the domain into a hyperplane, which is the extra condition in the paper's definition of M-concavity (p.9).
--
--   Differences from the source:
--   - encoding: an extension parallel network G with o,d-path set P → a family P of arc sets with IsEPFamily P (single arc / parallel union / arc in series); reason: the game depends on the network only through its path family; the grammar generates exactly the path families of EP networks
--   - generalization: cost functions c_e : ℤ≥0 → ℚ, non-negative and non-decreasing → c : E → ℕ → ℝ, non-negative and monotone; reason: rational costs are real costs, so the statement specializes to the paper's
--   - encoding: N = [n] (players, [k] defined for k ∈ ℤ>0) → hypothesis 0 < n; reason: the paper's implicit n ≥ 1
--   - reading: L = {α ∈ [q]ⁿ : |α| = n} → L = {α : P → ℕ | Σ_p α_p = n}; reason: the set is used as the set of strategy load profiles (one coordinate per path)
--   - encoding: M-convex: −Φ satisfies (5) and dom lies in {Σα = r} → MExchangeAxiom of Φ extended by ⊤ off L; reason: M-EXC with a nonempty domain implies the hyperplane condition, so the two definitions agree
--   - encoding: Φ(α) = Φ(s) for s ∈ S(α) (p.15, footnote 21) → loadPotential, the formula Σ_e Σ_{k=1}^{Σ_{p∋e} α_p} c_e(k); reason: ℓ_e(s) = Σ_{p∋e} z_p(s), so the formula takes the value Φ(s) on every s ∈ S(α)
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 4.1, p.15; M-convexity, §2.2, p.9

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_MExchangeAxiom
import Definitions.Def_GibbsCongestion_IsEPFamily
import Definitions.Def_GibbsCongestion_loadPotential

namespace GibbsCongestion

/-- **Proposition 4.1** (Fujishige et al.) (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, Proposition 4.1, p.15). For an extension
parallel congestion game, Rosenthal's potential on load profiles, `Φ : L → ℝ`,
`Φ(α) = Φ(s)` for `s ∈ S(α)`, is M-convex.

**Formalization Note** The network is encoded by its family `P` of o,d-paths (`IsEPFamily`);
players are `Fin n` with `0 < n`; profiles are `s : Fin n → P`. Costs are real valued,
non-negative and non-decreasing (the paper's standing assumption, p.7, with `ℚ` generalized to
`ℝ`). M-convexity (p.9) is Murota's exchange axiom M-EXC[ℤ]
(`DiscreteConvex.ConjugacyDualityD.MExchangeAxiom`) applied to `Φ` extended by `+∞` outside
`L = {α ∈ ℤ^P_{≥0} : ∑_p α_p = n}`; with a nonempty domain M-EXC implies that the domain lies in
a hyperplane, so this is the paper's M-convexity. -/
theorem proposition_4_1 {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset (Finset E)) (hP : IsEPFamily P) (n : ℕ) (hn : 0 < n)
    (c : E → ℕ → ℝ) (hc_nonneg : ∀ e k, 0 ≤ c e k) (hc_mono : ∀ e, Monotone (c e)) :
    DiscreteConvex.ConjugacyDualityD.MExchangeAxiom (fun α : P → ℤ =>
      if (∀ p, 0 ≤ α p) ∧ ∑ p, α p = (n : ℤ) then
        ((loadPotential c (fun p => (α p).toNat) : ℝ) : WithTop ℝ)
      else ⊤) := by sorry

end GibbsCongestion
