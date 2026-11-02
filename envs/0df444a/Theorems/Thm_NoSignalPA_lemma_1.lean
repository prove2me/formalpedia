-- Prove2me | Theorems.Thm_NoSignalPA_lemma_1
-- name    : NoSignalPA.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:04:53.697493+00:00
-- url     : https://prove2.me/theorems/bef9cc61-ad11-488d-93a6-6e2ba735b352
-- title:
--   Lemma 1 — $P_{\mathbf a|\mathbf x=\mathbf 0}=\langle\Gamma_{\mathbf a}|P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}\rangle$ (corrected: transposed tables)
-- statement:
--   Let $Q\in\mathbb R^{16^{N_r}}$, with entries $Q(\mathbf a,\mathbf b,\mathbf x,\mathbf y)$, satisfy the no-signaling equations of Alice's $N_r$ systems and of Bob taken as one system:
--
--   1. for each $i$, every $\mathbf x$, every bit $c$ and all $\mathbf a,\mathbf b,\mathbf y$: $\sum_{a_i}Q(\mathbf a,\mathbf b,\mathbf x,\mathbf y)=\sum_{a_i}Q(\mathbf a,\mathbf b,\mathbf x[x_i\mapsto c],\mathbf y)$;
--   2. $\sum_{\mathbf b}Q(\mathbf a,\mathbf b,\mathbf x,\mathbf y)$ does not depend on $\mathbf y$.
--
--   Then for every $\mathbf s\in\{0,1\}^{N_r}$ and every $\mathbf y$,
--
--   $$
--   \sum_{\mathbf b}Q(\mathbf s,\mathbf b,\mathbf 0,\mathbf y)=\langle\Gamma_{\mathbf s}|Q\rangle ,\qquad |\Gamma_{\mathbf s}\rangle=|\gamma_{s_1}\rangle\otimes\cdots\otimes|\gamma_{s_{N_r}}\rangle .
--   $$
--
--   For a nonsignaling box $Q=P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}$ the left side is Alice's marginal $P_{\mathbf a=\mathbf s|\mathbf x=\mathbf 0}$, so the probability of each raw key is a fixed linear functional of the box. The proof of the main result applies it to $P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}$ at fixed $e,z$.
--
--   Differences from the source:
--   - correction: |Γ_a⟩ built from the tables |γ₀⟩, |γ₁⟩ printed in Lemma 1 (p. 2) → |Γ_a⟩ built from their transposes (gammaCoef); reason: the printed tables are transposed relative to layout (3): for Nr = 1 and the nonsignaling box a = 1 ⊕ x, b = 0, P_{a=0|x=0} = 0 but the printed ⟨γ₀|P⟩ = 1; with the transposes Lemma 1 holds
--   - generalization: an (Nr + 1)-partite nonsignaling distribution P_{a,b|x,y} → any real vector Q satisfying the homogeneous no-signaling equations of Alice's Nr systems and of Bob as one system; reason: a nonsignaling box satisfies these equations; Q = P gives the paper's statement
--   - encoding: P_{a|x=0} → Σ_b Q(s, b, 0, y) for every y; reason: this is Alice's marginal; by Bob's no-signaling equation it does not depend on y
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Lemma 1, p.2 (proof in the Appendix, p.4)

import Mathlib
import Definitions.Def_NoSignalPA_pairing
import Definitions.Def_NoSignalPA_gammaVec

namespace NoSignalPA

/-- **Lemma 1 (corrected: transposed tables): `P_{a|x=0} = ⟨Γ_a|P_{a,b|x,y}⟩`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Lemma 1, p. 2 (PDF p. 2), proved in the Appendix, p. 4: "For any `(Nr + 1)`-partite
nonsignaling distribution `P_{a,b|x,y}` we have `P_{a|x=0} = ⟨Γ_a|P_{a,b|x,y}⟩`, where
`|Γ_a⟩ = |γ_{a1}⟩ ⊗ · · · ⊗ |γ_{aNr}⟩`".

Let `Q(a, b, x, y)` be any real vector of `ℝ^{16^{Nr}}` satisfying the homogeneous no-signaling
equations of Alice's `Nr` systems (`hA`) and of Bob as one system (`hB`). Then for every `s` and
every `y`, `Σ_b Q(s, b, 0, y) = ⟨Γ_s|Q⟩`.

**Formalization Note.** (1) Correction: `Γ_s` is built from the transposes of the printed
tables (`gammaCoef`); with the printed ones the lemma fails for the box `a = 1 ⊕ x`, `b = 0` at
`Nr = 1`. (2) Generalization: `Q` need not be nonnegative or normalized; a nonsignaling box
`P_{a,b|x,y}` is the case `Q = P`, and the left side is then `P_{a=s|x=0}` (read at any `y`). The
proof of the main result uses `Q = P_{a,b,e|x,y,z}` at fixed `e, z`. -/
theorem lemma_1 {Nr : ℕ} (Q : Str Nr → Str Nr → Str Nr → Str Nr → ℝ)
    (hA : ∀ (i : Fin Nr) (x : Str Nr) (c : Bool) (y a b : Str Nr),
      ∑ t : Bool, Q (Function.update a i t) b x y
        = ∑ t : Bool, Q (Function.update a i t) b (Function.update x i c) y)
    (hB : ∀ (a x y y' : Str Nr), ∑ b : Str Nr, Q a b x y = ∑ b : Str Nr, Q a b x y')
    (s y : Str Nr) :
    ∑ b : Str Nr, Q s b (fun _ => false) y = pairing (gammaVec s) Q := by sorry

end NoSignalPA
