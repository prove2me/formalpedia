-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_7_20
-- name    : GL2QFT.Supplement.theorem_7_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:45:59.028969+00:00
-- url     : https://prove2.me/theorems/1056e08b-b8fe-42e8-aa71-28ce6b8010d6
-- title:
--   Theorem 7.20 — Steps 3–8 of Algorithm 2 implement the right-coset induction transform (212)
-- statement:
--   Let $N\trianglelefteq G$ be finite groups, under the extension hypothesis (194) of Theorem 7.12. Fix the data of §7: representatives of $\widehat N$, orbit representatives $O(\widehat N)$, for $\sigma\in O(\widehat N)$ a transversal $T_\sigma=\{g_{\sigma,\mu}\}$ with $g_{\sigma,\sigma}=1$ (Definition 7.2) and orbit transport intertwiners $U_{t,\sigma}$ with $U_{1,\sigma}=\mathrm{id}$ (Definition 7.4), representatives of the irreps of the little groups $H_\sigma$, and a transversal $T_N$ of $N$ ($g=nh$). Then for every $\lambda\in\widehat N$, encoded as $(\sigma,t_L)$ with $\lambda=(t_L)\sigma$, Steps 3–8 of Algorithm 2 with $U^L_{\rm orb}$ omitted, acting on the right $N$-Fourier register and the coset register,
--   $$V^*_\lambda\otimes\mathbb C[T_N]\longrightarrow\bigoplus_{\eta'\in\widehat H_\sigma}\mathbb C^{d_{\eta'}}\otimes V^*_{(\sigma,\eta')},$$
--   equal the right-coset induction transform of Definition B.3,
--   $$[U^\lambda_{\rm Ind}]^{(\sigma,\eta'),j;\,t_R,k^*_\sigma,l^*_{\eta'}}_{k^*_\lambda,h}=\sqrt{\frac{d_{(\sigma,\eta')}}{d_\lambda|T_N|}}\;\langle k_\lambda:\lambda\xrightarrow{j}(\sigma,\eta')|R_{(\sigma,\eta')}(h)|t_R,k_\sigma,l_{\eta'}\rangle , \tag{212}$$
--   in the $N$-adapted basis (199) and the little group basis (198).
--
--   Differences from the source:
--   - encoding: "Steps 3–8 implement the right-coset induction transform on the right $N$-Fourier register" → for each $\lambda$, the product of the matrices of Steps 3–8 (without $U^L_{\rm orb}$) on $V^*_\lambda\otimes\mathbb C[T_N]$ equals (212); reason: the left $N$-Fourier register is untouched by these steps
--   - encoding: the classical Step 5, $h\mapsto(a,t_R)$ with $h=t_Lat_R^{-1}$ → the output $t_R$ occurs exactly when $t_L^{-1}ht_R\in I_\sigma$, with $a=t_L^{-1}ht_R$; reason: Definition 7.18's unique factorization
--   - encoding: Step 3 ($\lambda\mapsto(\sigma,t_L)$) and Step 7 ($a\mapsto(h_\sigma,d)$, uncompute $d$, relabel $h_\sigma\equiv aN$) → $(\sigma,t_L)$ taken as parameters with $\lambda=(t_L)\sigma$ (`IsOrbEnc`), and the coset $aN\in I_\sigma/N$ used directly as the input of $\mathfrak F_{H_\sigma}$; reason: classical relabellings whose outputs are determined by Definition 7.16 and Lemma 7.19
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 7.20, eq. (212), p.64 (PDF p.65); Algorithm 2 p.63; Definitions 7.14–7.18 pp.61–62; Definition B.3 p.82

import Definitions.Def_GL2QFT_Supplement_LittleGroup

open Classical

namespace GL2QFT

namespace Supplement

open LittleGroup

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 7.20**, p.64 (PDF p.65): "Under the
extension hypothesis of Theorem 7.12, Steps 3–8 of Algorithm 2, omitting `U^L_orb` in Step 4,
implement the right-coset induction transform in Definition B.3, on the right `N`-Fourier register."

Setting of §7 (pp.55–63): `N ⊴ G` finite; chosen representatives `R_λ` of `N̂`; a set `O` of orbit
representatives; for `σ ∈ O` a set `T_σ` of representatives of `g₁ ∼ g₂ ⟺ (g₁)σ = (g₂)σ` with
`g_{σ,σ} = 1`; orbit transport intertwiners `U_{t,σ}` normalized by `U_{1,σ} = id`; fixed extensions
`R^ext_λ` of every `R_λ` to `I_λ` (194); representatives `R_{η′}` of the duals of the little groups
`H_σ = I_σ / N`; a transversal `T_N` of `N` (`g = nh`). Then for every `λ`, encoded as `(σ, t_L)`
(`λ = (t_L)σ`), Steps 3–8 without `U^L_orb`, as an operator from `V*_λ ⊗ ℂ[T_N]` to
`⊕_{η′} ℂ^{d_{η′}} ⊗ V*_(σ,η′)`, equal the right-coset induction transform (212) in the `N`-adapted
basis (199) and the little group basis (198). -/
theorem theorem_7_20 {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
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
    (TN : Set G) (hTN : Subgroup.IsComplement (N : Set G) TN)
    (l σ : ΛN) (tL : Tσ σ) (henc : IsOrbEnc N BN RN O Tσ l σ (tL : G)) :
    stepsRight N BN RN Tσ U Rext Bη Rη TN l σ tL =
      uIndRight N BN RN Tσ U Rext Bη Rη TN l σ tL := by sorry

end Supplement

end GL2QFT
