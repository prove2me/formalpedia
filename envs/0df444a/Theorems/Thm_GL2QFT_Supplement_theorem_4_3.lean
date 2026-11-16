-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_4_3
-- name    : GL2QFT.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:41:38.094435+00:00
-- url     : https://prove2.me/theorems/383ac1ec-be6a-47db-b702-0ada8628dc1b
-- title:
--   Theorem 4.3 (Beals' construction) — $U_{\rm Ind}=W_nW_{n-1}\cdots W_1$ on valid inputs
-- statement:
--   Let $H\le G$ be finite groups, fix representatives $R_\lambda$ ($\lambda\in\widehat H$) and $R_\mu$ ($\mu\in\widehat G$) of the irreducible representations in orthonormal bases, the bases of the $R_\mu$ subgroup-adapted to $H$ (so restrictions are multiplicity-free), and a left transversal $T=\{\tau_1,\dots,\tau_n\}$ of $H$ containing $e$. Use the registers of Figure 7, an $H$-module register that encodes every $B_\lambda$ injectively, and any unitaries $U_\lambda$ with $U_\lambda|0\rangle=|\phi_\lambda\rangle$ (47). Then for every $k\in[n]$, $\lambda\in\widehat H$ and $P\in B_\lambda$,
--   $$W_nW_{n-1}\cdots W_1\,|\tau_k,P,\lambda,0,\lambda\rangle=|\star\rangle|\Psi_{k,P}\rangle|\lambda\rangle=U_{\rm Ind}|\tau_k,P,0,0,\lambda\rangle ,$$
--   with $W_k=R(\tau_k)UV_kU^\dagger R(\tau_k)^\dagger$ (52) and $|\Psi_{k,P}\rangle$ of (46). By linearity, $U_{\rm Ind}=\prod_{k=1}^nW_k$ on the span of the valid inputs, after the control $\lambda$ is copied into the fresh $H$-irrep register.
--
--   Beals' construction implements the induction transform with $n=[G:H]$ gate sandwiches, each acting nontrivially on one transversal element.
--
--   Differences from the source:
--   - reading: $R(\tau_k)$ "controlled by $\mu$ and the transversal register being $\star$" → acts on every joint state $|\star,Q,\tilde\lambda,\mu,c\rangle$ that encodes a label $Q:\tilde\lambda\to\mu$, whatever the control $c$; reason: Definition 4.1 names only these controls; on the states reached from valid inputs $\mu\in N^+(\lambda)$ always holds, so a reading that also checks the control gives the same products
--   - encoding: the identity on valid inputs spanned by the basis vectors → stated on each basis vector (after copying $\lambda$), with the image (45)–(46); reason: both sides are linear
--   - encoding: one wire encoding all $B_\lambda$, registers $\widehat G\sqcup\{0\}$, $\widehat H\sqcup\{0\}$, $T\sqcup\{\star\}$ → any finite register with injective encodings of the $B_\lambda$, and `Option` registers; reason: the paper fixes no encoding; the statement covers every one
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 4.3, eq. (53), pp.25–26 (PDF pp.26–27); §4 eqs. (45)–(52) pp.23–25

import Definitions.Def_GL2QFT_Supplement_Beals
import Definitions.Def_GL2QFT_Supplement_RepTheory

open Classical

namespace GL2QFT

namespace Supplement

open Induction Beals

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 4.3 (Beals' construction)**,
pp.25–26 (PDF pp.26–27): "On valid inputs spanned by basis vectors `|τ_k, P, 0, 0, λ⟩`, with
`k ∈ [n]` and `P ∈ B_λ` for `λ ∈ Ĥ`, the induction transform `U_Ind` can be decomposed as
`U_Ind = ∏_{k=1}^n W_k = W_n W_{n−1} ⋯ W_1` (53), after setting the fresh `H`-irrep register `|0⟩`
equal to the control register `|λ⟩`. Here, `W_k` is defined in Equation (52)."

Setting of §4 (p.23): `H ≤ G` finite, `R_λ` (`λ ∈ Ĥ`) and `R_μ` (`μ ∈ Ĝ`) chosen representatives of
the irreps in orthonormal bases, the bases of the `R_μ` subgroup-adapted ((35)); `T = {τ_1, …, τ_n}`
a left transversal of `H` containing `e`; an `H`-module register `Mod` encoding every `B_λ`
injectively; and any admissible unitaries `U_λ` with `U_λ|0⟩ = |ϕ_λ⟩` (47). Then for every `k`, every
`λ` and every `P ∈ B_λ`, `W_n ⋯ W_1 |τ_k, P, λ, 0, λ⟩ = |⋆⟩|Ψ_{k,P}⟩|λ⟩`, the image (45)–(46) of
`|τ_k, P, 0, 0, λ⟩` under `U_Ind`; by linearity the two maps agree on the span of these inputs.

**Formalization Note** The registers are `Option T × Mod × Option Ĥ × Option Ĝ × Ĥ` (see `Reg`);
`τ : Fin n ≃ T` is any enumeration of `T`. The multiplicity-freeness of `Res^G_H` is built into the
subgroup-adapted labels `B_μ = {P : λ → μ | λ ∈ N⁻(μ)}`. -/
theorem theorem_4_3 {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] (T : Set G)
    [Fintype T] (hT : Subgroup.IsComplement T (H : Set G)) (he : (1 : G) ∈ T)
    {ΛH ΛG : Type} [Fintype ΛH] [Fintype ΛG] (BH : ΛH → Type) [∀ l, Fintype (BH l)]
    [∀ l, DecidableEq (BH l)] (Nminus : ΛG → Finset ΛH)
    (RH : ∀ l, H → Matrix (BH l) (BH l) ℂ) (hRH : IsIrrepSystem RH)
    (RG : ∀ μ, G → Matrix (AdBas BH Nminus μ) (AdBas BH Nminus μ) ℂ) (hRG : IsIrrepSystem RG)
    (hAd : IsSubgroupAdapted H BH Nminus RH RG)
    (Mod : Type) [Fintype Mod] (emb : ∀ l, BH l → Mod) (hemb : ∀ l, Function.Injective (emb l))
    (Ul : ΛH → Matrix (Option ΛG) (Option ΛG) ℂ) (hUl : IsAdmissibleU T BH Nminus Ul)
    (τ : Fin (Fintype.card T) ≃ T) (k : Fin (Fintype.card T)) (l : ΛH) (P : BH l) :
    (Wprod T BH Nminus Mod emb RG Ul τ).mulVec (ket T Mod (some (τ k), emb l P, some l, none, l)) =
      bealsTarget T BH Nminus Mod emb RG (τ k) l P := by sorry

end Supplement

end GL2QFT
