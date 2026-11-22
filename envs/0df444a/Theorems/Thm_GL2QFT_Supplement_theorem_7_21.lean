-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_7_21
-- name    : GL2QFT.Supplement.theorem_7_21
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T01:46:39.593203+00:00
-- url     : https://prove2.me/theorems/de0cb7cf-a9ba-4b1f-9b44-6d609e852459
-- title:
--   Theorem 7.21 — Algorithm 2 implements $\mathfrak F_G$ in the little group basis
-- statement:
--   Let $N\trianglelefteq G$ be finite groups, under the extension hypothesis (194), with the data of §7 as in Theorem 7.20. Algorithm 2 (Steps 1–8: $g=nh$; $\mathfrak F_N$; $\lambda\mapsto(\sigma,t_L)$; the orbit transport gates $U^L_{\rm orb}$, $U^R_{\rm orb}$; $h=t_Lat_R^{-1}$; $(R^{\rm ext}_\sigma)^*(a^{-1})$; $a\mapsto aN$; $\mathfrak F_{H_\sigma}$), with output $|\sigma,\eta'\rangle\otimes|t_L,i_\sigma,j_{\eta'}\rangle\otimes|t_R,k^*_\sigma,l^*_{\eta'}\rangle$, implements the Fourier transform of Proposition 2.7:
--   $$\mathrm{Alg}_2=\mathfrak F_G,\qquad \mathfrak F_G|g\rangle=\sum_{(\sigma,\eta')}\sqrt{\frac{d_{(\sigma,\eta')}}{|G|}}\sum_{x,y}[R_{(\sigma,\eta')}(g)]^x_y\,|(\sigma,\eta'),x,y^*\rangle ,$$
--   for the irreps $R_{(\sigma,\eta')}=\mathrm{Ind}^G_{I_\sigma}(R^{\rm ext}_\sigma\otimes\tilde R_{\eta'})$ in the little group basis $x,y\in\{|t,i_\sigma,j_{\eta'}\rangle\}$ (198), with all phases one.
--
--   This is the formal version of Theorem 1.3: a QFT for $G$ from QFTs for $N$ and the little groups.
--
--   Differences from the source:
--   - encoding: Algorithm 2 → the product of its steps' matrices, the classical steps entering as the unique solutions they compute; reason: the operator the algorithm applies
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 7.21, p.65 (PDF p.66); Algorithm 2 p.63; Proposition 2.7 eq. (22) p.14

import Definitions.Def_GL2QFT_Supplement_LittleGroup

open Classical

namespace GL2QFT

namespace Supplement

open LittleGroup

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 7.21**, p.65 (PDF p.66): "Algorithm 2
implements the Fourier transform of Proposition 2.7 using the little group basis."

Setting of §7 as in `theorem_7_20`, under the extension hypothesis (194) of Theorem 7.12 (in force
throughout §7.3). The operator of Algorithm 2 (Steps 1–8), with output
`|σ, η′⟩ ⊗ |t_L, i_σ, j_{η′}⟩ ⊗ |t_R, k*_σ, l*_{η′}⟩`, equals the Fourier transform (22) of `G` (all
phases one) for the irreps `R_(σ,η′) = Ind^G_{I_σ}(R^ext_σ ⊗ R̃_{η′})`, `σ ∈ O`, `η′ ∈ Ĥ_σ`, written in
the little group basis (198). -/
theorem theorem_7_21 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (Tσ : ΛN → Set G) (hTσ : ∀ σ ∈ O, IsLabelTransversal N BN RN Tσ σ)
    (U : ∀ σ : ΛN, G → ∀ l : ΛN, Matrix (BN l) (BN σ) ℂ)
    (hU : IsOrbitTransport N BN RN O Tσ U)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    (TN : Set G) (hTN : Subgroup.IsComplement (N : Set G) TN) :
    alg2 N BN RN O Tσ U Rext Bη Rη TN =
      fourierMatrix (fun p : GLab O (Λη := Λη) =>
        littleRep N BN RN Tσ Rext Bη Rη p.1.1 p.2) := by sorry

end Supplement

end GL2QFT
