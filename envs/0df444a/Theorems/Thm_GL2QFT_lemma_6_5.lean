-- Prove2me | Theorems.Thm_GL2QFT_lemma_6_5
-- name    : GL2QFT.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:41.66588+00:00
-- url     : https://prove2.me/theorems/c2f16ce1-52d4-4213-ba82-950f34c0a811
-- title:
--   Lemma 6.5 — irreducibility, splitting and isomorphism classes of the principal series $I_{\alpha,\beta}$
-- statement:
--   Let $I_{\alpha,\beta}$ be the principal series representation (94) of $\mathrm{GL}_2(\mathbb F_q)$ on $\mathbb C[\mathcal P^1(\mathbb F_q)]$, $\alpha,\beta\in X_q$.
--   1. If $\alpha\neq\beta$, then $I_{\alpha,\beta}$ is irreducible.
--   2. If $\alpha=\beta$, then $I_{\alpha,\alpha}$ splits into the line $\det_\alpha$ spanned by $|v\rangle=(q+1)^{-1/2}(\chi_\alpha(-1)|\infty\rangle+\sum_x|x\rangle)$ and its orthogonal complement, the Steinberg representation $\mathrm{St}_\alpha$. Both are invariant, and $\mathrm{St}_\alpha$ is irreducible.
--   3. $I_{\alpha,\beta}\cong I_{\gamma,\delta}$ if and only if $(\alpha,\beta)=(\gamma,\delta)$ or $(\alpha,\beta)=(\delta,\gamma)$.
--
--   Together with the cuspidal representations, this classifies the irreps of $\mathrm{GL}_2(\mathbb F_q)$ (Table 2).
--
--   Differences from the source:
--   - reading: "it splits into a one-dimensional and a Steinberg representation" → the span of $|v\rangle$ (97) and its orthogonal complement are invariant, and the complement is irreducible; reason: the paper names the one-dimensional piece $|v\rangle$ and defines $\mathrm{St}_\alpha$ as its orthogonal complement (p.36), and lists it among the irreducible representations
--   - encoding: labels $\alpha,\beta\in X_q$ → exponent labels in $\mathbb Z/(q-1)\mathbb Z$; reason: Remark 6.2
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma 6.5, p.35 (PDF p.36); eqs. (94)–(98) pp.35–36

import Definitions.Def_GL2QFT_Irreps

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma 6.5**, p.35 (PDF p.36): "The principal
series `I_{α,β}` is irreducible whenever `α ≠ β`. Otherwise, it splits into a one-dimensional and a
Steinberg representation. Moreover, `I_{α,β}` and `I_{γ,δ}` are isomorphic if and only if
`[α = γ, β = δ]` or `[α = δ, β = γ]`."

`I_{α,β}` is the model (94) on `ℂ[P¹(F_q)]` (`psModel`), for all labels `α, β` (any order). The
three clauses are:
1. `α ≠ β` ⟹ `I_{α,β}` is irreducible;
2. `I_{α,α}` splits into the line spanned by `|v⟩` (97) (`detVec`, the determinant representation)
   and its orthogonal complement `St_α` (p.36): both are invariant, and `St_α` is irreducible (it has
   no invariant subspace other than `0` and itself);
3. `I_{α,β} ≅ I_{γ,δ}` iff `(α, β) = (γ, δ)` or `(α, β) = (δ, γ)`. -/
theorem lemma_6_5 (D : FieldData) :
    (∀ α β : D.Lab, α ≠ β →
      IsIrreducibleRep (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))) ∧
    (∀ α : D.Lab,
      let I := fun g : D.G => D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)
      let v := D.detVec α
      (∀ g : D.G, ∃ c : ℂ, (I g).mulVec v = c • v) ∧
      (∀ (g : D.G) (u : Option D.Fq → ℂ), dotProduct (star v) u = 0 →
        dotProduct (star v) ((I g).mulVec u) = 0) ∧
      (∀ W : Submodule ℂ (Option D.Fq → ℂ), (∀ u ∈ W, dotProduct (star v) u = 0) →
        IsInvariantSubspace I W →
        W = ⊥ ∨ ∀ u : Option D.Fq → ℂ, dotProduct (star v) u = 0 → u ∈ W)) ∧
    (∀ α β γ δ : D.Lab,
      RepEquiv (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))
          (fun g : D.G => D.psModel γ δ (g : Matrix (Fin 2) (Fin 2) D.Fq)) ↔
        (α = γ ∧ β = δ) ∨ (α = δ ∧ β = γ)) := by sorry

end GL2QFT
