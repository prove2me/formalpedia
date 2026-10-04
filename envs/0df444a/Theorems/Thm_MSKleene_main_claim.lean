-- Prove2me | Theorems.Thm_MSKleene_main_claim
-- name    : MSKleene.main_claim
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-08T12:37:34.795681+00:00
-- url     : https://prove2.me/theorems/b9ca05a1-5439-43bc-9696-9bd2a9a5c939
-- title:
--   Claim 4.13 (Main Claim): the auxiliary languages are regular
-- statement:
--   **The auxiliary languages are regular** (Claim 4.13 (Main Claim)).
--
--   In the recognition context of the proof of Proposition 4.10: for every $u\in S$, every $C\subseteq N$, every $K\subseteq N$ with $K\le N$, and every $l\in n_{u}$, there exists a regular expression $R_{u}(C,K,l)\in\mathrm{T}_{\mathrm{Reg}(S,\Sigma,Z)}(Z)_{u}$ with $\{R_{u}(C,K,l)\}^{Z\sharp}_{u}=L_{u}(C,K,l)$; that is, the languages $L_{u}(C,K,l)$ are $u$-regular. Proved by induction on the budget size $\|\|K\|\|=\sum_{s}k_{s}$.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

import Definitions.Def_MSKleene_AuxLang

namespace MSKleene

/-- **Main Claim** (Claim 4.13).

In the recognition context `ctx` of the proof of Proposition 4.10, for every
sort `u`, every set `C ⊆ N` of leaf-admissible states, every sortwise budget
`K ≤ N`, and every target state `l ∈ N_u`, the auxiliary language
`L_u(C,K,l)` is `u`-regular over `Z`: there is a regular expression `R` of type
`u` over `(S,Σ,Z)` with `{R}^{Z♯}_u = L_u(C,K,l)`. -/
theorem main_claim {S : Type} [Finite S] (sig : Signature S) (X : SSet S)
    (hsig : SigFinite sig) (hX : SFinite X) (ctx : KleeneCtx sig X) (u : S)
    (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ) (hK : ∀ s, K s ≤ ctx.n s)
    (l : Fin (ctx.n u)) :
    ∃ R : RegExpr sig ctx.Z u,
      interpExpr sig ctx.Z u R = ctx.auxLang u C K l := by
  sorry

end MSKleene
