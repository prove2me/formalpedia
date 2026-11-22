-- Prove2me | Theorems.Thm_MasulloGRH_ideleNorm_relativeIdeleNorm
-- name    : MasulloGRH.ideleNorm_relativeIdeleNorm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:54.244715+00:00
-- url     : https://prove2.me/theorems/2a347742-4be5-43f6-ae63-b71ac4a1b29a
-- title:
--   Lemma A.2.2.2, diagram (A.2.2.5) — the idelic norm is compatible with the relative norm of ideles: $|N_{L/K}(g)|_K=|g|_L$
-- statement:
--   **Compatibility of the idelic norm with the relative norm of ideles** (Lemma A.2.2.2, diagram (A.2.2.5) of the source, for an arbitrary extension of number fields).
--
--   Let $L/K$ be an extension of number fields, of degree $[L:K]$, with adele rings $\mathbb A_K$, $\mathbb A_L$ and idele groups $\mathbb I_K=\mathrm{GL}_1(\mathbb A_K)$, $\mathbb I_L=\mathrm{GL}_1(\mathbb A_L)$. The canonical continuous ring homomorphism $i_{L/K}\colon\mathbb A_K\to\mathbb A_L$ extending $K\hookrightarrow L$ makes $\mathbb A_L\cong\mathbb A_K\otimes_KL$ a free $\mathbb A_K$-algebra of rank $[L:K]$; let
--   $$N_{L/K}\colon\mathbb A_L\to\mathbb A_K$$
--   be the associated algebra norm (the determinant of multiplication by an adele of $L$ on the free $\mathbb A_K$-module $\mathbb A_L$). It is multiplicative, hence induces a homomorphism $N_{L/K}\colon\mathbb I_L\to\mathbb I_K$ of idele groups, and likewise $i_{L/K}$ induces $i_{L/K}\colon\mathbb I_K\to\mathbb I_L$. Let $|g|_L=\prod_w|g_w|_w$ and $|h|_K=\prod_v|h_v|_v$ be the idelic norms of $L$ and $K$ (products of the normalized absolute values over all places). Then for every idele $g\in\mathbb I_L$
--   $$\big|N_{L/K}(g)\big|_K=|g|_L ,$$
--   i.e. the square
--   $$\begin{array}{ccc}\mathbb I_L&\xrightarrow{\ |\cdot|_L\ }&\mathbb R_{>0}\\ {\scriptstyle N_{L/K}}\downarrow&&\|\\ \mathbb I_K&\xrightarrow{\ |\cdot|_K\ }&\mathbb R_{>0}\end{array}$$
--   commutes. No Galois hypothesis is needed.
--
--   The source states this for $K=\mathbb Q$, $L=F$ (the norm $N_{F/\mathbb Q}\colon\mathrm{GL}_1(\mathbb A_F)\to\mathrm{GL}_1(\mathbb A_{\mathbb Q})$) and uses it to transport the canonical section $s_{\mathbb Q}$ of the idelic norm of $\mathbb Q$ to the canonical section $s_F=i_F\circ s_{\mathbb Q}\circ(\cdot)^{1/[F:\mathbb Q]}$ of the idelic norm of $F$ (Definition A.2.2.3, Lemma A.2.2.4). The general statement is the adelic form of the local identities $|N_{L_w/K_v}(x)|_v=|x|_w$ for the normalized absolute values, and it is the reason why the norm map of class field theory $C_L\to C_K$ preserves the idelic norm.
--
--   **Deviation from the source.** The source takes $K=\mathbb Q$ and does not define $N_{F/\mathbb Q}$; the statement is given for an arbitrary extension $L/K$ of number fields, which specializes to the source for $K=\mathbb Q$.
--
--   **Formalization Note.** The base change is the platform datum `M4aHerbrand.GenuineDescent.genuineBaseChange K L : AdeleBaseChange (𝓞 K) K (𝓞 L) L`: its field `β` is the ring homomorphism $i_{L/K}\colon\mathbb A_K\to\mathbb A_L$ (it is continuous and restricts to $K\hookrightarrow L$ on principal adeles, which characterizes it), and `idelicNorm` is `Units.map` of `Algebra.norm (AdeleRing (𝓞 K) K)` for the algebra structure induced by `β`; the datum also contains an isomorphism $\mathbb A_K\otimes_KL\cong\mathbb A_L$ of $\mathbb A_K$-algebras, so $\mathbb A_L$ is finite free over $\mathbb A_K$ and `Algebra.norm` is the genuine norm. The idelic norms are the platform's `MasulloGRH.ideleNorm` for $K$ and for $L$ (explicit products of norms of the completions, with `‖·‖ ^ mult` at the infinite places). `[Algebra K L]` is the only hypothesis: finite-dimensionality is automatic for number fields.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 546, Lemma A.2.2.2, diagram (A.2.2.5)

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField

set_option autoImplicit false

namespace MasulloGRH

theorem ideleNorm_relativeIdeleNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (g : IdeleGroup L) :
    ideleNorm ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm g) =
      ideleNorm g := by sorry

end MasulloGRH
