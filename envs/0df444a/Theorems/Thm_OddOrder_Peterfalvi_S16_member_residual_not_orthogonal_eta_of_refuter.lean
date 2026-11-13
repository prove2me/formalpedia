-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_member_residual_not_orthogonal_eta_of_refuter
-- name    : OddOrder.Peterfalvi.S16.member_residual_not_orthogonal_eta_of_refuter
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:17:34.946669+00:00
-- url     : https://prove2.me/theorems/4b8f0a21-d3b0-4cb6-b393-68317dbb8d81
-- title:
--   Peterfalvi (11.8): the Section 12 residual of a degree-$w_1$ member is not orthogonal to the $\eta$-grid
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `base : S15.Hypothesis` a Peterfalvi §13 configuration with $T=$ `base.T`, subgroups $W, W_1,W_2$ and $\eta$-grid ($i<q$, $j<p$), and let `s12 : S12.Hypothesis base.T` be the Section 12 hypothesis for $T$ with type-$P$ datum `s12.typeP`. Assume:
--
--   - the $W$-data agree: `s12.typeP.W = base.W`, `s12.typeP.W2 = base.W1`, `s12.typeP.W1 = base.W2`;
--   - `typePV T s12.typeP` equals the set $W\setminus(W_1\cup W_2)$;
--   - $T$ is of type III or type IV;
--   - the second derived subgroup of $T$ equals $H\sqcup(U\cap C_G(H))$ (`s12.typeP.H ⊔ (s12.typeP.U ⊓ centralizer H)`);
--   - $|H|=w_2^{\,w_1}$;
--   - (`hrefute`) for every §13 hypothesis `s13hyp` on $T$, there is no coherence datum `S07.IsCoherent s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0`;
--   - $\zeta$ is an irreducible character of $T$ in the induced family `S12.inducedFamily T` with $\zeta(1)=w_1$;
--   - `source` is a class function on $G$ with $\tau\bigl(\sum_{i'<w_1}\mu\mathrm{Grid}_{i',0}-\zeta\bigr)=\text{source}$, where $\tau=$ `s12.tau`.
--
--   Then it is not the case that all grid pairings of the residual vanish:
--   $$\neg\ \forall i<q,\ \forall j<p:\quad \Bigl\langle\ \text{source}-\sum_{j'<p}\eta_{0j'},\ \eta_{ij}\Bigr\rangle=0 .$$
--
--   This transports the canonical refuter of `S13.zeta_residual_not_orthogonal_H0C_of_refuter` through the global $\sigma$/$\eta$ grid identification. The Dade-image identification of the source is the input `himage`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean#L1280-L1341

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem member_residual_not_orthogonal_eta_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (s12 : OddOrder.Peterfalvi.S12.Hypothesis base.T)
    (hW : s12.typeP.W = base.W)
    (hW1 : s12.typeP.W2 = base.W1)
    (hW2 : s12.typeP.W1 = base.W2)
    (hV : typePV base.T s12.typeP =
      (base.W : Set G) \ ((base.W1 : Set G) ∪ (base.W2 : Set G)))
    (htype : IsTypeIII base.T ∨ IsTypeIV base.T)
    (hM2 : secondDerivedInAmbient base.T =
      s12.typeP.H ⊔
        (s12.typeP.U ⊓ Subgroup.centralizer (s12.typeP.H : Set G)))
    (hHcard : Nat.card ↥s12.typeP.H = s12.w2 ^ s12.w1)
    (hrefute : ∀ s13hyp : OddOrder.Peterfalvi.S13.Hypothesis base.T,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    (zeta : ClassFunction ↥base.T ℂ)
    (hzetaS : zeta ∈ OddOrder.Peterfalvi.S12.inducedFamily base.T)
    (hzetairr : IsIrreducibleCharacter zeta)
    (hzeta1 : zeta 1 = (s12.w1 : ℂ))
    (source : ClassFunction G ℂ)
    (himage : s12.tau
        ((∑ i' : Fin s12.w1, s12.muGrid hG hG.odd i' 0) - zeta) = source) :
    ¬ ∀ (i : Fin base.q) (j : Fin base.p),
      ClassFunction.inner
        (source - ∑ j' : Fin base.p, base.eta ⟨0, base.q_prime.pos⟩ j')
        (base.eta i j) = 0 := by sorry

end OddOrder.Peterfalvi.S16
