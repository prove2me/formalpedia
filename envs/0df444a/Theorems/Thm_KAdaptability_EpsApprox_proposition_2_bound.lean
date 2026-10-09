-- Prove2me | Theorems.Thm_KAdaptability_EpsApprox_proposition_2_bound
-- name    : KAdaptability.EpsApprox.proposition_2_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:23.145264+00:00
-- url     : https://prove2.me/theorems/a6d8f3bb-6bb5-4741-8272-b9fc23d98fff
-- title:
--   Proof of Proposition 2, (a)–(d), p. ec7 — |φ_ε − φ| ≤ (max_ℓ max_ξ dist(ξ, Ξ_ε(ℓ))) · max_k ‖Cx + Qy^k‖
-- statement:
--   Fix a decision $(x,\{y^k\}_{k\in\mathcal K})\in\mathrm{dom}(6)$, i.e. a decision in $\mathcal X\times\mathcal Y^K$ whose objective value in problem (6) is not $+\infty$, and $\varepsilon>0$ such that $\Xi_\varepsilon(\ell)\ne\emptyset$ for every $\ell\in\mathcal L$ with $\Xi(\ell)\ne\emptyset$. Let $\varphi$ and $\varphi_\varepsilon$ be the objective values of the decision in (6) and in $(6_\varepsilon)$. Then $\varphi$ and $\varphi_\varepsilon$ are real numbers and
--   $$|\varphi_\varepsilon-\varphi|\ \le\ \Big(\max_{\ell\in\mathcal L:\ \Xi(\ell)\ne\emptyset}\ \sup_{\xi\in\Xi(\ell)}\ \inf_{\xi'\in\Xi_\varepsilon(\ell)}\|\xi-\xi'\|\Big)\cdot\Big(\max_{k\in\mathcal K}\|Cx+Qy^k\|\Big),$$
--   with the Euclidean norm.
--
--   The first factor is controlled by Lemma 1 and the second is bounded because $\mathcal X$ and $\mathcal Y$ are finite; together they give the uniform convergence in Proposition 2.
--
--   **Formalization Note** The paper assumes "$\varepsilon>0$ small enough so that $\mathrm{dom}(6_\varepsilon)=\mathrm{dom}(6)$", a property its proof obtains from Lemma 1 as "$\Xi_\varepsilon(\ell)\ne\emptyset$ if and only if $\Xi(\ell)\ne\emptyset$". The Lean statement assumes this nonemptiness property directly for the fixed decision, which is what the chain (a)–(d) uses (in step (b) the minimum is over $\Xi_\varepsilon(\ell)$). The outer maximum ranges over the $\ell$ with $\Xi(\ell)\ne\emptyset$ (a maximum over an empty set contributes nothing); it is a real supremum (`⨆`) of the bounded family `Metric.infDist ξ (Ξ_ε(ℓ))` over $\xi\in\Xi(\ell)$, and $\max_k$ is a supremum over `Fin K`. The conclusion asserts the finiteness of both objective values by exhibiting real numbers equal to them.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec7 (PDF p. 41), proof of Proposition 2, chain (a)–(d)

import Mathlib
import Definitions.Def_KAdaptability_EpsApprox_Approx

namespace KAdaptability.EpsApprox

open Problem Matrix

/-- **Proof of Proposition 2, bound (a)–(d)** (p. ec7). Fix a decision
`(x, {y^k}_{k∈𝒦}) ∈ dom(6)` and `ε > 0` small enough that `Ξ_ε(ℓ) ≠ ∅` for every `ℓ ∈ ℒ` with
`Ξ(ℓ) ≠ ∅` (the property the first part of the proof derives from Lemma 1). Then the objective
values `φ` of (6) and `φ_ε` of (6_ε) are real numbers and
`|φ_ε − φ| ≤ (max_{ℓ∈ℒ} max_{ξ∈Ξ(ℓ)} min_{ξ′∈Ξ_ε(ℓ)} ‖ξ − ξ′‖) · (max_{k∈𝒦} ‖Cx + Qy^k‖)`,
with Euclidean norms and the outer maximum taken over the `ℓ` with `Ξ(ℓ) ≠ ∅`. -/
theorem proposition_2_bound {N M L nQ R K : ℕ} (P : Problem N M L nQ R)
    (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (hd : (x, y) ∈ P.dom6 K)
    (ε : ℝ) (hε : 0 < ε)
    (hsmall : ∀ ℓ : Fin K → Fin (L + 1),
      (P.XiL x y ℓ).Nonempty → (P.XiEps ε x y ℓ).Nonempty) :
    ∃ φ φε : ℝ, P.obj6 x y = (φ : EReal) ∧ P.obj6Eps ε x y = (φε : EReal) ∧
      |φε - φ| ≤
        (⨆ ℓ : {ℓ : Fin K → Fin (L + 1) // (P.XiL x y ℓ).Nonempty},
            ⨆ ξ : P.XiL x y ℓ.1, Metric.infDist (ξ : EuclideanSpace ℝ (Fin nQ))
              (P.XiEps ε x y ℓ.1)) *
          (⨆ k : Fin K,
            ‖(WithLp.toLp 2 (P.C *ᵥ x + P.Q *ᵥ y k) : EuclideanSpace ℝ (Fin nQ))‖) := by sorry

end KAdaptability.EpsApprox
