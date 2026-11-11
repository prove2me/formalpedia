-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_4_3
-- name    : LabelSymmetricCollision215.Collision.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:52.053204+00:00
-- url     : https://prove2.me/theorems/92d3a26c-87ab-4ee3-b260-b0b6774ae7d8
-- title:
--   Lemma 4.3 — Symmetry and the orbit-span space bound
-- statement:
--   Let $G$ be any finite group acting unitarily on the input register, $\delta$ any input distribution, and $A$ any $T$-query algorithm with algorithm dimension at most $2^S$. Suppose $\pi(g)\rho_I^t\pi(g)^\dagger=\rho_I^t$ for every $g$ and every checkpoint. For every $t$ and every vector $\beta$ in the support of $\rho_I^t$,
--   $$\dim\operatorname{span}\{\pi(g)\beta:g\in G\}\le2^S.$$
--   This retains the general group and distribution of the source.
--
--   Differences from the source:
--   - encoding: zero start, WXY order and negative-exponent Fourier basis → published fixed unit start, XYW coordinates, with the value register explicitly changed to the same Fourier basis; reason: absorb fixed state preparation into U₀ and permute basis factors; neither operation changes queries, dimensions, or measured success
--   - generalization: S qubits of algorithm space → real S with algorithm dimension at most 2^S; reason: the source uses only its displayed dimension charge, so every integer qubit budget is recovered by substitution
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 4.3, PDF 22 / printed 20

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 4.3, PDF 22 / printed 20. -/
theorem lemma_4_3 {M N T : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (A : Alg M N T W) (S : ℝ) (hspace : UsesSpace M N W S)
    {G : Type} [Group G] [Fintype G]
    (π : G →* Matrix.unitaryGroup (Input M N) ℂ) (δ : PMF (Input M N))
    (hsym : ∀ t g, (π g : Matrix _ _ ℂ) * reduced (jointState A δ t) *
      star (π g : Matrix _ _ ℂ) = reduced (jointState A δ t))
    (t : Fin (T+1)) (β : H (Input M N))
    (hβ : β ∈ (mat (reduced (jointState A δ t))).toLinearMap.range) :
    (Module.finrank ℂ (orbitSpan (fun g => (mat (π g : Matrix _ _ ℂ)).toLinearMap) β) : ℝ)
      ≤ (2 : ℝ)^S := by sorry

end LabelSymmetricCollision215.Collision
