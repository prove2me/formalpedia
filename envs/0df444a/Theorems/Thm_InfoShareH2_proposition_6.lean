-- Prove2me | Theorems.Thm_InfoShareH2_proposition_6
-- name    : InfoShareH2.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:46.796797+00:00
-- url     : https://prove2.me/theorems/24e40f20-5fbe-4987-887b-4ffb381bc2c9
-- title:
--   Proposition 6 — $\sigma^2_{S|FI}=(B(0)G(0))^2\sigma^2_{S|NS}\le\sigma^2_{S|NS}$, with equality iff $\tilde\psi$ is outer
-- statement:
--   Let $\sigma_\epsilon>0$ and let $\tilde\psi\in\tilde\Psi$ have the factorization $\tilde\psi=QBG$ of Lemma 2: $Q$ the outer part, $B$ a Blaschke product with zeros $z_k$ and $m_0$ zeros at the origin, and $G$ a singular inner function with measure $\mu$ and constant $1$. Then $\sigma^2_{S|FI}(\tilde\psi)=(\sigma_\epsilon\tilde\psi(0))^2$ and $\sigma^2_{S|NS}(\tilde\psi)=(\sigma_\epsilon Q(0))^2$, and
--
--   $$\sigma^2_{S|FI}(\tilde\psi)=\bigl(B(0)G(0)\bigr)^2\sigma^2_{S|NS}(\tilde\psi)\le\sigma^2_{S|NS}(\tilde\psi),\qquad |B(0)|=0^{m_0}\prod_k|z_k|,\quad |G(0)|=e^{-\mu(\mathbb T)}.$$
--
--   Moreover:
--
--   1. $B(0)=1$ if and only if $B\equiv1$ on the disk;
--   2. $G(0)=1$ if and only if $G$ is constant on the disk;
--   3. $\sigma^2_{S|FI}(\tilde\psi)=\sigma^2_{S|NS}(\tilde\psi)$ if and only if $\tilde\psi$ is outer;
--   4. $\sigma^2_{S|FI}(\tilde\psi)<\sigma^2_{S|NS}(\tilde\psi)$ (positive value of information sharing) if and only if $\tilde\psi$ is not outer.
--
--   This is the paper's exact measure of the value of information sharing for a given order policy, and the proof of Theorem 2 uses the inequality to relax (26).
--
--   Differences from the source:
--   - reading: any ψ̃ ∈ H² → ψ̃ ∈ Ψ̃ (real coefficients) and σ_ε > 0; reason: Assumption 1 is standing from p.26 ("we do not restate but indeed assume"); σ²_S|FI and σ²_S|NS are defined for order policies
--   - reading: "the factorization ψ̃ = QBG defined in Lemma 2" → Q the outer part, B Blaschke data carrying the unimodular constant, G singular inner with constant 1, ψ̃ = QBG on D; reason: the normalization of Lemma 2; under it every clause holds as printed
--   - reading: "{z_n} the sequence of zeros of B", |B(0)| = ∏_{n≥1}|z_n| → |B(0)| = 0^{m₀}·∏_k |z_k|; reason: the zero at the origin has multiplicity m₀
--   - reading: "positive value of information sharing" → σ²_S|FI < σ²_S|NS; reason: value of sharing is the reduction of the supplier’s MSFE
--   - encoding: (σ_ε ψ̃(0))², (σ_ε Q(0))², (B(0)G(0))², µ(T) → identities in ℂ; µ(univ).toReal; reason: Lean convention; B(0)G(0) and Q(0) are real here
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Proposition 6, p.30, (42) (proof §9.13, p.50)

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

namespace InfoShareH2

/-- **Proposition 6 (value of information sharing).**
SSRN 4319721 (v. 2024-01-20), Proposition 6, p.30, (42) (proof §9.13, p.50). "For any `ψ̃ ∈ H²`
with the factorization `ψ̃(z) = Q(z)B(z)G(z)` defined in Lemma 2, denote by `{z_n}` the sequence of
zeros of `B(z)` in the disk `D`. Then, since `σ²_S|FI(ψ̃) = (σ_ε ψ̃(0))²` and
`σ²_S|NS(ψ̃) = (σ_ε Q(0))²`, we have `σ²_S|FI(ψ̃) = (B(0)G(0))² σ²_S|NS(ψ̃) ≤ σ²_S|NS(ψ̃)`, where
`|B(0)| = ∏_{n≥1} |z_n|`, `|G(0)| = exp(−µ(T))`. Moreover, `B(0) = 1` if and only if `B(z) ≡ 1`,
and `G(0) = 1` if and only if `G(z)` is a constant. Consequently, `σ²_S|FI(ψ̃) = σ²_S|NS(ψ̃)` if and
only if `ψ̃` is an outer function, and there is (positive) value of information sharing if and only
if `ψ̃` is not outer."

**Formalization Note** Stated for `ψ̃ ∈ Ψ̃` (Assumption 1 is standing from p.26; real coefficients)
and `σ_ε > 0`. The factorization is the one of Lemma 2: `Q` is the outer part, `B` a Blaschke
product carrying the unimodular constant, `G` a singular inner function with constant `1`. The zeros
of `B` are its zeros `z_k` together with `0` counted `m₀` times, so `∏_n |z_n| = 0^{m₀} ∏_k |z_k|`.
"Positive value of information sharing" is `σ²_S|FI < σ²_S|NS`. -/
theorem proposition_6 (σε : ℝ) (hσε : 0 < σε) (ψ : ℕ → ℝ) (hψ : ψ ∈ PsiTilde)
    (B : BlaschkeData) (G : SingularData) (hG : G.c = 1)
    (hfac : ∀ z ∈ Disk,
      zTransform (ofRealSeq ψ) z = outerPart (ofRealSeq ψ) z * B.eval z * G.eval z) :
    ((fsVar σε ψ : ℂ) = ((σε : ℂ) * zTransform (ofRealSeq ψ) 0) ^ 2) ∧
    ((nsVar σε ψ : ℂ) = ((σε : ℂ) * outerPart (ofRealSeq ψ) 0) ^ 2) ∧
    ((fsVar σε ψ : ℂ) = (B.eval 0 * G.eval 0) ^ 2 * (nsVar σε ψ : ℂ)) ∧
    fsVar σε ψ ≤ nsVar σε ψ ∧
    ‖B.eval 0‖ = (0 : ℝ) ^ B.m0 * ∏' k, ‖B.zs k‖ ∧
    ‖G.eval 0‖ = Real.exp (-(G.μ Set.univ).toReal) ∧
    (B.eval 0 = 1 ↔ ∀ z ∈ Disk, B.eval z = 1) ∧
    (G.eval 0 = 1 ↔ ∃ c : ℂ, ∀ z ∈ Disk, G.eval z = c) ∧
    (fsVar σε ψ = nsVar σε ψ ↔ IsOuter (ofRealSeq ψ)) ∧
    (fsVar σε ψ < nsVar σε ψ ↔ ¬ IsOuter (ofRealSeq ψ)) := by sorry

end InfoShareH2
