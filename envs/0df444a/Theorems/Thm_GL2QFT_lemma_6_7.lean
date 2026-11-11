-- Prove2me | Theorems.Thm_GL2QFT_lemma_6_7
-- name    : GL2QFT.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:55.218208+00:00
-- url     : https://prove2.me/theorems/8bb4b8c5-2ad9-4070-a1e5-f4c750c12928
-- title:
--   Lemma 6.7 — restrictions along $T<B<\mathrm{GL}_2(\mathbb F_q)$, realized in the Gelfand–Tsetlin bases
-- statement:
--   In the explicit models and Gelfand–Tsetlin bases of §6.1–6.2 the restrictions of Lemma 6.7 hold as equalities of matrices.
--   1. (102) $\chi_{\alpha,\beta}\begin{pmatrix}a&0\\0&d\end{pmatrix}=\chi_\alpha(a)\chi_\beta(d)$.
--   2. (103) $\rho_\gamma\begin{pmatrix}a&0\\0&d\end{pmatrix}$ is diagonal in the basis (108), with entries $\chi_\delta(a)\chi_{\delta^{-1}\gamma}(d)$; thus $\mathrm{Res}^B_T\rho_\gamma=\bigoplus_\delta\chi_{\delta,\delta^{-1}\gamma}$.
--   3. (104) $\det_\alpha$ restricts to $\chi_{\alpha,\alpha}$ on $B$.
--   4. (105) On $B$, $\mathrm{St}_\alpha$ is block diagonal: $\chi_{\alpha,\alpha}$ on $|v^\perp\rangle$ and $\rho_{\alpha^2}$ on the $|w_\delta\rangle$.
--   5. (106) On $B$, $I_{\alpha,\beta}$ ($\alpha\prec\beta$) is block diagonal: $\chi_{\alpha,\beta}$ on $|\infty\rangle$, $\chi_{\beta,\alpha}$ on $|v_0\rangle$, $\rho_{\alpha\beta}$ on the $|w_\delta\rangle$.
--   6. (107) On $B$, $\pi_\theta=\rho_\gamma$ with $\theta|_{\mathbb F_q^*}=\chi_\gamma$.
--   7. (Multiplicity-free) The characters $\chi_{\delta,\delta^{-1}\gamma}$ of $T$ in (103) are pairwise distinct. The summands $\chi_{\alpha,\alpha}$ and $\rho_{\alpha^2}$ of (105) are inequivalent as representations of $B$, and so are any two of the summands $\chi_{\alpha,\beta}$, $\chi_{\beta,\alpha}$, $\rho_{\alpha\beta}$ of (106), $\alpha\neq\beta$.
--
--   These branching rules show that the bases of §6.2 are subgroup-adapted along $T<B<G$, which is what the induction method of §3 and the Mackey circuit of §5 require.
--
--   **Formalization Note** "$\cong$" is realized by the identity map in the Gelfand–Tsetlin bases: the restricted matrix equals the block matrix. Multiplicity-freeness is expressed by the inequivalence of the summands.
--
--   Differences from the source:
--   - generalization: isomorphisms of restricted representations (102)–(107) → equalities of the restricted matrices with the block-diagonal matrices in the Gelfand–Tsetlin bases; reason: an explicit decomposition implies the isomorphism, and the paper's §6.2 asserts exactly these adapted bases
--   - reading: "restriction along the chain is multiplicity-free" → the $T$-characters in (103) are pairwise distinct and the $B$-summands in (105), (106) are pairwise inequivalent; reason: given the decompositions 1–6, multiplicity-freeness means exactly that the summands are pairwise inequivalent
--   - encoding: $\delta^{-1}\gamma$, $\alpha^2$, $\alpha\beta$ → the exponent labels $\gamma-\delta$, $2\alpha$, $\alpha+\beta$; reason: Remark 6.2, labels are exponents
--   - reading: (106) for every $\alpha\neq\beta$ and (107) for every regular $\theta$ → (106) for the representative $I_{\alpha,\beta}$ with $\alpha\prec\beta$ (exponent order) in the basis (110), and (107) for the chosen representative of each orbit $\{\theta,\theta^q\}$; reason: Lemma 6.7 is about the irreducible representations of Table 2, i.e. isomorphism classes, and p.44 represents each principal series by $I_{\alpha,\beta}$ with $\alpha\prec\beta$ ($I_{\alpha,\beta}\cong I_{\beta,\alpha}$ by Lemma 6.5, and the right side of (106) is symmetric in $\alpha,\beta$); $\pi_\theta$ and $\pi_{\theta^q}$ have the same matrices in this model
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Lemma 6.7 eqs. (102)–(107), p.37 (PDF p.38); §6.2.1–6.2.2 pp.37–39

import Definitions.Def_GL2QFT_Irreps

open Classical

namespace GL2QFT

open FieldData

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Lemma 6.7**, p.37 (PDF p.38): "The following
restrictions of irreducible representations hold:
`Res^B_T χ_{α,β} = χ_{α,β}` (102), `Res^B_T ρ_γ = ⊕_{δ∈X_q} χ_{δ,δ⁻¹γ}` (103),
`Res^G_B det_α = χ_{α,α}` (104), `Res^G_B St_α = χ_{α,α} ⊕ ρ_{α²}` (105),
`Res^G_B I_{α,β} = χ_{α,β} ⊕ χ_{β,α} ⊕ ρ_{αβ}`, `α ≠ β` (106),
`Res^G_B π_θ = ρ_γ`, `θ|_{F*_q} = χ_γ` (107).
In particular, restriction along the chain `T < B < GL₂(F_q)` is multiplicity-free."

Stated in the explicit models and Gelfand–Tsetlin bases, so that every `≅` is realized by the
basis (as in §6.2): for `g ∈ T` (diagonal) resp. `g ∈ B` (upper triangular), the matrix of the
restriction is block diagonal with the stated blocks, in this order:
1. (102) `χ_{α,β}(diag(a, d)) = χ_α(a)χ_β(d)`;
2. (103) `ρ_γ(diag(a, d))` is diagonal in (108) with entries `χ_δ(a) χ_{δ⁻¹γ}(d)`;
3. (104) `R_{det_α}(g) = χ_{α,α}(g)` on `B`;
4. (105) `R_{St_α}(g)` on `B`: `χ_{α,α}` on `|v^⊥⟩`, `ρ_{α²}` (in (108)) on the `|w_δ⟩`, zero across;
5. (106) `R_{I_{α,β}}(g)` on `B`, `α ≺ β`: `χ_{α,β}` on `|∞⟩`, `χ_{β,α}` on `|v₀⟩`, `ρ_{αβ}` on the
   `|w_δ⟩`, zero across;
6. (107) `R_{π_θ}(g) = ρ_γ(g)` on `B`, `γ = γ(k)`;
7. (multiplicity-free) the `T`-characters in (103) are pairwise distinct, and the `B`-summands in
   (105) and in (106) are pairwise inequivalent as representations of `B`. -/
theorem lemma_6_7 (D : FieldData) :
    (∀ (α β : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 →
      D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () () =
        D.chi α ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) * D.chi β ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) ∧
    (∀ (γ : D.Lab) (g : D.G) (δ δ' : D.Lab), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 →
      D.RB (.inr γ) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ' =
        if δ = δ' then D.chi δ ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
          D.chi (γ - δ) ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) else 0) ∧
    (∀ (α : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      D.R (.inl α) g () () = D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()) ∧
    (∀ (α : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : Option D.Lab, D.R (.inr (.inl α)) g i j =
        match i, j with
        | none, none => D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some δ, some δ' => D.RB (.inr (2 * α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ'
        | _, _ => 0) ∧
    (∀ (ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) (g : D.G),
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : Option (Option D.Lab), D.R (.inr (.inr (.inl ab))) g i j =
        match i, j with
        | none, none => D.RB (.inl (ab.1.1, ab.1.2)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some none, some none => D.RB (.inl (ab.1.2, ab.1.1)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some (some δ), some (some δ') =>
            D.RB (.inr (ab.1.1 + ab.1.2)) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ'
        | _, _ => 0) ∧
    (∀ (k : {k : D.Lab2 // D.IsCuspLabel k}) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : D.Lab, D.R (.inr (.inr (.inr k))) g i j =
        D.RB (.inr (D.restrLab k.1)) (g : Matrix (Fin 2) (Fin 2) D.Fq) i j) ∧
    ((∀ γ δ δ' : D.Lab, δ ≠ δ' → ∃ g : D.G, (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 ∧
        D.chi δ ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) * D.chi (γ - δ) ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) ≠
          D.chi δ' ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
            D.chi (γ - δ') ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) ∧
      (∀ α : D.Lab, ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
          (fun g : D.G => D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
          (fun g : D.G => D.RB (.inr (2 * α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))) ∧
      (∀ α β : D.Lab, α ≠ β →
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inl (β, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq)) ∧
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inr (α + β)) (g : Matrix (Fin 2) (Fin 2) D.Fq)) ∧
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (β, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inr (α + β)) (g : Matrix (Fin 2) (Fin 2) D.Fq)))) := by sorry

end GL2QFT
