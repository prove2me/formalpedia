-- Prove2me | Theorems.Thm_GL2QFT_lemma_3_5
-- name    : GL2QFT.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:08.16118+00:00
-- url     : https://prove2.me/theorems/1c1a4bf5-7de7-4286-bb0a-a611de065159
-- title:
--   Lemma 3.5 — $\mathfrak F_G=(U_{\mathrm{Ind}}\otimes I)(I_{\mathbb C[T]}\otimes\mathfrak F_H)\,\mathrm{Enc}$
-- statement:
--   Let $H$ be a subgroup of a finite group $G$ and $\mathcal T$ a left transversal, so every $g\in G$ is uniquely $g=th$ with $t\in\mathcal T$, $h\in H$. Let $(R_\lambda)$ be a family of representations of $H$ in bases $\mathcal B_\lambda$. Let $(R_\mu)$ be a family of representations of $G$ in subgroup-adapted bases $\mathcal B_\mu=\{P:\lambda\to\mu\mid\lambda\in N^-(\mu),P\in\mathcal B_\lambda\}$, i.e. satisfying (35). Then the Fourier transforms (22) of the two families satisfy
--   $$\mathfrak F_G=(U_{\mathrm{Ind}}\otimes I)\,(I_{\mathbb C[\mathcal T]}\otimes\mathfrak F_H)\,\mathrm{Enc}.$$
--   Here a basis vector $|\lambda,Q:\tilde\lambda\to\mu,R^*\rangle$ of the right-hand codomain is identified with $|\mu,Q:\tilde\lambda\to\mu,(R:\lambda\to\mu)^*\rangle$, and this identification is a bijection.
--
--   The lemma reduces the QFT of $G$ to the QFT of $H$ and the induction transform. The proof of Theorem 6.1 applies it to $B<\mathrm{GL}_2(\mathbb F_q)$, eq. (146).
--
--   **Formalization Note** The identity is stated for arbitrary families of representations with adapted labels. The paper's families are complete sets of pairwise inequivalent irreducible unitary representations, in which case both sides are the Fourier transforms of Definition 2.6.
--
--   Differences from the source:
--   - generalization: complete families of pairwise inequivalent irreducible unitary representations of $H$ and $G$, multiplicity-free restriction → any families of matrix representations (homomorphisms) with subgroup-adapted labels satisfying (35); reason: the proof uses only (35), multiplicativity of $R_\mu$ and $|G|=|\mathcal T||H|$, and the paper's families are instances
--   - encoding: the implicit identification of codomain basis vectors → an explicit map `ident`, asserted to be a bijection, under which the rows are re-indexed; reason: the same identification made explicit
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma 3.5, eq. (43), pp.19–20 (PDF pp.20–21)

import Definitions.Def_GL2QFT_InductionTransform

open Classical

namespace GL2QFT

open Induction

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma 3.5**, p.19 (PDF pp.20–21): "With
`H < G`, `T`, `B_λ` for all `λ ∈ Ĥ` and `B_μ` for all `μ ∈ Ĝ` as before, the Fourier transform `F_G`
of `G` from Definition 2.6 factors as `F_G = (U_Ind ⊗ I)(I_{ℂ[T]} ⊗ F_H) Enc` (43). Here, we have
`Enc` from Definition 3.2, `U_Ind` from Definition 3.3 and the subgroup Fourier transform `F_H`. In
this equation, we implicitly identify a basis vector `|λ, Q : λ̃ → μ, R*⟩` of the codomain of the
right hand side with the basis vector `|μ, Q : λ̃ → μ, (R : λ → μ)*⟩` of the codomain of the left
hand side."

For a finite group `G`, a subgroup `H`, a left transversal `T` (`g = th` uniquely), a family `R_λ`
of `H` in bases `B_λ`, and a family `R_μ` of representations of `G` in subgroup-adapted bases
`B_μ = {P : λ → μ | λ ∈ N⁻(μ), P ∈ B_λ}` satisfying (35): the identification `ident` is a bijection
and `F_G` (22) equals `(U_Ind ⊗ I)(I ⊗ F_H) Enc` with its rows re-indexed by `ident`. -/
theorem lemma_3_5 {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (T : Set G)
    [Fintype T] (hT : Subgroup.IsComplement T (H : Set G))
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ)
    (hRG : ∀ μ, IsMatRep (RG μ)) (hAd : IsSubgroupAdapted H BH Nminus RH RG) :
    Function.Bijective (ident BH Nminus) ∧
    fourierMatrix RG =
      ((UIndTensorI T BH Nminus RG * Matrix.kronecker (1 : Matrix T T ℂ) (fourierMatrix RH)) *
        Enc H T).submatrix (ident BH Nminus) id := by sorry

end GL2QFT
