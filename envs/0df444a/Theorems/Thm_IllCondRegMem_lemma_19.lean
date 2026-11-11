-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_19
-- name    : IllCondRegMem.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:36.305461+00:00
-- url     : https://prove2.me/theorems/c9aabf7a-65e5-4970-bf8d-a1412f787013
-- title:
--   Lemma 19 — from masked covariances to the correct spectrum: $P_G(\lambda^2P_{F_1}+\rho\lambda^2P_{F_2})P_G=P_G(\lambda^2P_Y)P_G$
-- statement:
--   Let $d=8q$ and $\rho\in(0,1)$, and let $\lambda\in\mathbb R$. Let $E\subseteq\mathbb R^d$ be a subspace of dimension $d_E=3d/4$, $G\subseteq E^\perp$ a subspace of dimension at most $d/8$, and $Y\subseteq\mathbb R^d$ a subspace with
--   $$
--   P_GP_YP_G\succeq\rho P_G .
--   $$
--   Then there is a subspace $F_1=F_1(E,G,Y)\subseteq E^\perp$ of dimension $d/8$ such that, with $F_2=(E\oplus F_1)^\perp$,
--   $$
--   P_G\big(\lambda^2P_{F_1}+\rho\lambda^2P_{F_2}\big)P_G=P_G\big(\lambda^2P_Y\big)P_G .
--   $$
--   The degenerate masked covariance $P_E+\lambda^2P_Y$ thus has the same compression onto the explored subspace $G$ as a full-rank covariance with the spectrum $(1,\lambda^2,\rho\lambda^2)$ used by the rotational adversary.
--
--   **Formalization Note** Operators are continuous linear maps; $A\succeq B$ means $\langle x,Ax\rangle\ge\langle x,Bx\rangle$ for all $x$.
--
--   Differences from the source:
--   - reading: E ∈ Gr(d_E, d) and ρ, with d_E and ρ fixed earlier in the paper → d = 8q, dim E = 6q (d_E = 3d/4), ρ ∈ (0,1); reason: standing values of eqs. (1), (56) and of Lemma 6, which the proof applies on E⊥
--   - encoding: deterministic choice F₁ = F₁(E, G, Y) → existence of F₁ for each (E, G, Y); reason: a choice function exists for each triple; same content
--   - encoding: matrices, ⪰ → continuous linear maps, quadratic-form inequalities; reason: Lean representation; same instances
--   - generalization: λ ∈ (0, 1), the standing range of eq. (1) → any real λ; reason: both sides scale by λ², so the identity for λ ∈ (0,1) is the instance λ ∈ (0,1) of the Lean statement
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 19, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory

namespace IllCondRegMem

/-- **Lemma 19 (From masked covariances to correct spectrum).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 19,
p.25: "Fix E ∈ Gr(d_E, d), a subspace G ⊆ E⊥ of dimension at most d/8, and a subspace Y ⊆ ℝ^d such
that P_G P_Y P_G ⪰ ρP_G. Then there is deterministic choice F₁ = F₁(E, G, Y) ⊆ E⊥ of dimension
d/8, such that, with F₂ = (E ⊕ F₁)⊥, P_G(λ²P_{F₁} + ρλ²P_{F₂})P_G = P_G(λ²P_Y)P_G."

**Formalization Note.** The standing values of the paper are used: `d_E = 3d/4` (eqs. (1),
(56)), so `d = 8q` and `dim E = 6q`, and `ρ ∈ (0, 1)` (§3, the range of Lemma 6); `λ` is any
real number. "Deterministic choice" is the existence of `F₁` for each `(E, G, Y)`. Operators are
continuous linear maps, `P_F` is `F.starProjection`, and `A ⪰ B` is `⟨x, Ax⟩ ≥ ⟨x, Bx⟩` for
all `x`. -/
theorem lemma_19 (d q : ℕ) (hd : d = 8 * q) (ρ lam : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (E G Y : Submodule ℝ (Vec d)) (hE : Module.finrank ℝ E = 6 * q) (hGE : G ≤ Eᗮ)
    (hG : Module.finrank ℝ G ≤ q)
    (hY : ∀ x, ρ * inner ℝ x (G.starProjection x) ≤
      inner ℝ x ((G.starProjection ∘L Y.starProjection ∘L G.starProjection) x)) :
    ∃ F₁ : Submodule ℝ (Vec d), F₁ ≤ Eᗮ ∧ Module.finrank ℝ F₁ = q ∧
      G.starProjection ∘L (lam ^ 2 • F₁.starProjection + (ρ * lam ^ 2) • (E ⊔ F₁)ᗮ.starProjection)
          ∘L G.starProjection =
        G.starProjection ∘L (lam ^ 2 • Y.starProjection) ∘L G.starProjection := by sorry

end IllCondRegMem
