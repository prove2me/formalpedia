-- Prove2me | Theorems.Thm_MayersQKD_lemma_1
-- name    : MayersQKD.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:47:10.908447+00:00
-- url     : https://prove2.me/theorems/19efc815-5ea0-45b3-8f01-c219eaa187d8
-- title:
--   Lemma 1, p.10 — no information under the small distance property (corrected: $f$ of full row rank)
-- statement:
--   Let $v$ be a view with an accepted test, a pair $(E_0,E_1)$ and $c=1$, so that $E_c=E_1$, and let $f$ be the matrix in $v$. Suppose that
--
--   $$
--   2\epsilon n<\mathrm{wt}(y^{\mathsf T}f)\quad\text{for every nonzero }y\in\mathrm{GF}(2)^{r+m},
--   $$
--
--   and that $M_v$ has the $\epsilon n$-small distance property. Then $v$ provides no information at all on the string $b$:
--
--   $$
--   p(v\mid b)=p(v\mid b')\quad\text{for all }b,b'.
--   $$
--
--   This is the exact form of secrecy. The test of the protocol only delivers the small distance property approximately, which is the subject of §10.
--
--   Differences from the source:
--   - correction: εn < dN/2 with dN the minimum distance of C₀⊥ → 2εn < wt(yᵀf) for every nonzero y; reason: false as printed: n = 9, N = 2, r = 0, m = 2, f = ((1,1),(1,1)), so C₀⊥ = {00, 11}, dN = 2, εn < 1; an honest Bob in the bases θ̂ has the small distance property, yet t₁ = t₂ gives a₁ ⊕ a₂ = b₁ ⊕ b₂ in every view, so p(v|b) = 0 for some b only. For f of full row rank the two hypotheses coincide
--   - generalization: Mᵥ built from a rank-one |v⟩⟨φᵥ| → K_y(t) M_ŵ any operator; reason: the rank-one case is an instance; the conclusion also holds for a coarser final measurement
--   - encoding: "provides no information at all on the string b" → p(v|b) equal for all b; reason: this is what the proof on p.10 sets out to show
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, Lemma 1, p.10

import Mathlib
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_transcript
import Definitions.Def_MayersQKD_HasSmallDistance

namespace MayersQKD

/-- Mayers, arXiv:quant-ph/9606003v1, Lemma 1, p.10 (corrected): if `2εn < wt(yᵀ f)` for every
nonzero `y`, `c = 1` and `M_v` has the `εn`-small distance property, then the outcome `v` provides no
information at all on the string `b`: `p(v|b)` is the same for all `b`.

**Formalization Note.** The view is `v = (t, y)` with `t` the transcript of an accepted test, a pair
`(E₀, E₁)` and `c = 1`, so `E_c = E₁`. The printed hypothesis is `εn < dN/2` with `dN` the minimum
distance of `C₀⊥`. That is false for rank-deficient `f` (correction C1); for `f` of full row rank the
hypothesis here is the printed one. `K_y(t) M_ŵ` is any operator, rank one being the case of p.9. -/
theorem lemma_1 {n r m : ℕ} (A : Attack n r m) (δ ε : ℝ) (s : A.Seed) (what : Bits n)
    (R : Finset (Fin n)) (θ : Bases n) (E0 E1 : Finset (Fin n))
    (f : HashMatrix r m (blockLen n)) (sv : Bits r) (av : Bits m) (u : Bits n) (y : A.Y)
    (hd : ∀ z : Fin r ⊕ Fin m → ZMod 2, z ≠ 0 →
      2 * (ε * n) < (hammingNorm (Matrix.vecMul z f) : ℝ))
    (hsd : HasSmallDistance A δ ε s what R f true E1
      (s, what, R, some (θ, some ((E0, E1), true, f, sv, av, u))) y)
    (b b' : Bits m) :
    viewProb A δ b ((s, what, R, some (θ, some ((E0, E1), true, f, sv, av, u))), y) =
      viewProb A δ b' ((s, what, R, some (θ, some ((E0, E1), true, f, sv, av, u))), y) := by sorry

end MayersQKD
